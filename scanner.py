#!/usr/bin/env python3
"""
Signal OPS IRL v5.0 (Tool edition)

Passive BLE advertisement dashboard: layered device identification, tactical /
ALPR / drone flagging with confidence tiers, a personal "known devices"
registry with permanent rename and ignore support (by MAC or by advertised name), RSSI trend + distance estimate,
interactive device inspector (c / Enter), live clock / battery / Bluetooth-adapter status line,
session scan-time tracking, hunt mode (hot/cold locator) and tracker follower detection,
sound notifications, switchable views (grid / compact / tactical / security watch / one per category),
signal-strength filtering, a JSON device/OUI/category config,
and MAC-randomization-resistant "ghost" fingerprinting that links a device's rotating
private addresses back to the same identity (and inherits any name you've already given it).

Live visual effects: new-device flash, alert-tier pulse, a sweeping radar view, hunt-mode sonar, an HUD heartbeat,
an animated XP bar with a shimmer sweep, and optional CRT scanlines (o toggles them, z toggles the motion).
An HTML session report is written automatically on exit (see --report-dir / --no-report).
Progression: XP, levels, daily quests, bounties, achievements and titles (press p). All content lives in
lookout_game.json, which you can edit while the scanner runs (see --check-game, --no-game).

Intel Coins: a second currency earned by quests, bounties, achievements, level-ups, streaks, tactical finds, hunts and scan time. Press e for the Coin
Exchange and trade them for hacker interface themes (Matrix, Amber CRT, Cyber Ice ...), neon mode, glitch effects and more. Prices, rewards and caps
live in lookout_game.json (coin_rules, coin_caps, shop); --check-game validates them. ALERT-red stays red in every theme.

Level-ups, quests, bounties, achievements and title unlocks trigger large centred full-screen celebration effects, each with its
own sound (level_up, quest_complete, bounty_claimed, achievement, title_unlock, streak_milestone, shop_unlock + .wav/.mp3/.ogg/.flac). An optional 'intro' sound plays at launch and every other sound waits until it ends. geiger_tick is the hunt-mode Geiger click. z toggles, --test-fx previews.

Boot sequence: once the Bluetooth adapter has started, a short startup sequence (adapter handshake, database loading, a loading bar and an
ACCESS GRANTED banner) plays the 'intro' sound. Any key skips it; --no-boot skips it for one run; the "boot" block of lookout_game.json tunes it.

Session complete: quitting shows a recap screen (time online, devices seen, XP earned, level, streak, coins, milestones) with the 'shutdown' sound.
--no-outro skips it, --test-outro previews it.

Mission mode: press y (with the inspector closed) for timed challenges such as "find 5 different vendors in 3 minutes". A countdown runs in the top bar; finishing in time pays
XP and Intel Coins and counts toward quests, achievements and titles (missions_completed). Missions live in lookout_game.json ("missions").

Daily hooks (reasons to come back every day): a Daily Surge (bonus XP in your first minutes of scanning each day), Streak Shields that
cover a missed day, a coin ladder on every streak day, Daily Caches (loot boxes for finishing quests), Weekly Ops with a Weekly Chest,
and a Welcome Back bonus. All of it is tuned in the "retention" block of lookout_game.json.

Requires: pip install bleak rich
Optional: pip install bluetooth-numbers      (full Bluetooth SIG company list)
Run once: python3 scanner.py --update-db   (IEEE OUI + SIG databases)
"""
from __future__ import annotations

import argparse
import asyncio
import bisect
import collections
import colorsys
import csv
import datetime
import fnmatch
import glob
import hashlib
import html as html_lib
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import textwrap
import threading
import time
import types
import urllib.request
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path

try:
    import termios, tty, select
    HAVE_TTY = True
except ImportError:                                   # Windows
    HAVE_TTY = False
try:
    import bleak
except ImportError:
    bleak = None
try:
    from rich.align import Align
    from rich.box import DOUBLE, ROUNDED
    from rich.cells import cell_len
    from rich.color import Color, ColorType
    from rich.console import Console, Group
    from rich.layout import Layout
    from rich.live import Live
    from rich.panel import Panel
    from rich.segment import Segment
    from rich.style import Style
    from rich.table import Table
    from rich.terminal_theme import TerminalTheme
    from rich.text import Text
    HAVE_RICH = True
except ImportError:
    HAVE_RICH = False

VERSION = "5.0-Tool"
KNOWN_FILE = "lookout_known.json"
CONFIG_FILE = "scanner_config.json"
SETTINGS_FILE = "lookout_settings.json"
CACHE_DIR = Path.home() / ".cache" / "lookout"
ACTIVE_WINDOW = 5.0                         # seconds: "● live" vs "○ recent"

# =============================================================================
# HELPERS & SOUND NOTIFICATIONS
# =============================================================================
def clean(s, limit=64) -> str:
    """Names come from strangers' radios: strip control chars / escape codes."""
    return "".join(c for c in str(s or "") if c.isprintable()).strip()[:limit]

def norm(s: str) -> str:
    return re.sub(r"[\s_]+", " ", s.lower()).strip()

def build_rx(terms):
    return re.compile(r"(?<![a-z])(?:" + "|".join(terms) + r")(?![a-z])", re.I)

MAC_RE = re.compile(r"^[0-9A-F]{2}(:[0-9A-F]{2}){5}$")
BASE_UUID = "-0000-1000-8000-00805f9b34fb"

def short_uuid(u: str) -> str:
    u = u.lower()
    if u.endswith(BASE_UUID):
        return u[4:8].upper() if u.startswith("0000") else u[:8].upper()
    return u[:8].upper() + "…"

def addr_kind(mac: str, props: dict) -> str:
    """public / static-random / private-resolvable / private-nonresolvable / unknown"""
    if not MAC_RE.match(mac):
        return "unknown"
    t = str(props.get("AddressType", "")).lower()
    if t == "public":
        return "public"
    if t == "random":
        top = int(mac[:2], 16) >> 6
        return {3: "static-random", 1: "private-resolvable", 0: "private-nonresolvable"}.get(top, "random")
    return "unknown"

def est_distance_ft(rssi: float, tx_power) -> float:
    """Log-distance model reference."""
    if rssi >= 0:
        return 0.0
    ref = (tx_power - 41) if tx_power is not None else -59
    return round(10 ** ((ref - rssi) / 25.0) * 3.28084, 1)

SOUND_EXTS = ("", ".wav", ".mp3", ".ogg", ".flac")
LINUX_PLAYERS = {"paplay": [], "aplay": ["-q"], "ffplay": ["-nodisp", "-autoexit", "-loglevel", "quiet"], "mpg123": ["-q"]}

def find_sound(base: str):
    """Path of <base>[.wav|.mp3|.ogg|.flac] in the current folder or the script's folder, or None."""
    for folder in (Path("."), Path(__file__).resolve().parent):
        for ext in SOUND_EXTS:
            p = folder / (base + ext)
            if p.is_file():
                return str(p)
    return None

INTRO = {"proc": None, "until": 0.0, "started": 0.0}
INTRO_MAX_SECONDS = 60.0     # safety cap: never keep the other sounds blocked longer than this

def intro_playing() -> bool:
    """True while the launch intro sound is still playing (every other sound waits for it)."""
    if not INTRO["started"] or time.time() - INTRO["started"] > INTRO_MAX_SECONDS:
        return False
    proc = INTRO["proc"]
    if proc is not None and proc.poll() is None:
        return True
    return time.time() < INTRO["until"]

def play_notification_sound(name: str = "notify", intro: bool = False):
    """Play the sound file called `name` (cross-platform); fall back to 'notify', then the terminal bell.
    While the launch intro is playing, every other sound is skipped."""
    if MUTED:
        return
    if not intro and intro_playing():
        return
    if not intro and name != "boot" and BOOT.get("active"):         # the boot sequence has the stage: no other sound until it is over
        return
    sound_path = find_sound(name) or (find_sound("notify") if name != "notify" and not intro else None)
    if intro and not sound_path:
        return                                                     # no intro file: stay silent, block nothing
    if sound_path:
        try:
            if sys.platform == "darwin":
                proc = subprocess.Popen(["afplay", sound_path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                if intro:
                    INTRO.update(proc=proc, started=time.time())
            elif sys.platform == "win32":
                import winsound
                winsound.PlaySound(sound_path, winsound.SND_ASYNC | winsound.SND_FILENAME)
                if intro:                                          # winsound has no handle: use the .wav length
                    try:
                        import wave
                        with wave.open(sound_path) as w:
                            INTRO.update(until=time.time() + w.getnframes() / float(w.getframerate()), started=time.time())
                    except Exception:
                        pass
            else:
                for player, extra in LINUX_PLAYERS.items():
                    if shutil.which(player):
                        proc = subprocess.Popen([player, *extra, sound_path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                        if intro:
                            INTRO.update(proc=proc, started=time.time())
                        break
                else:
                    sys.stdout.write("\a")
                    sys.stdout.flush()
        except Exception:
            sys.stdout.write("\a")
            sys.stdout.flush()
    else:
        sys.stdout.write("\a")
        sys.stdout.flush()

def play_shutdown_sound():
    """shutdown.(mp3|wav|ogg|flac): plays once as the scanner closes (q, Esc or Ctrl+C). No file = silence (no notify fallback).
    Respects the mute key. The player keeps running after the scanner exits, except on Windows where it is given time to finish."""
    if SHUTDOWN["played"]:
        return
    SHUTDOWN["played"] = True
    path = find_sound("shutdown")
    if not path or MUTED:
        return
    INTRO.update(proc=None, until=0.0, started=0.0)               # an intro still playing must not swallow it
    BOOT["active"] = False
    play_notification_sound("shutdown")
    if sys.platform == "win32":
        try:
            import wave
            with wave.open(path) as w:
                time.sleep(min(6.0, w.getnframes() / float(w.getframerate())))
        except Exception:
            pass

# -----------------------------------------------------------------------------
# Geiger ticks for hunt mode: geiger_tick.(wav|mp3|ogg|flac) fires at random (Poisson) intervals that
# speed up and get louder as the target gets closer. A small background thread keeps the timing smooth
# whatever the screen frame rate is. No file = the old terminal-bell beep.
# -----------------------------------------------------------------------------
GEIGER = {"path": "?", "thread": None}
GEIGER_SLOWEST = 1.6      # average seconds between ticks when far away
GEIGER_FASTEST = 0.15     # average seconds between ticks right on top of the target

def geiger_path():
    if GEIGER["path"] == "?":
        GEIGER["path"] = find_sound("geiger_tick")
    return GEIGER["path"]

def _play_geiger_tick(path: str, close: float):
    vol = 0.35 + 0.65 * max(0.0, min(1.0, close))                  # quieter when far, full volume up close
    try:
        if sys.platform == "darwin":
            subprocess.Popen(["afplay", "-v", f"{vol:.2f}", path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        elif sys.platform == "win32":
            import winsound
            winsound.PlaySound(path, winsound.SND_ASYNC | winsound.SND_FILENAME)
        else:
            volume_args = {"paplay": [f"--volume={int(65536 * vol)}"], "ffplay": ["-volume", str(int(100 * vol))],
                           "mpg123": ["-f", str(int(32768 * vol))]}
            for player, extra in LINUX_PLAYERS.items():
                if shutil.which(player):
                    subprocess.Popen([player, *extra, *volume_args.get(player, []), path],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    break
    except Exception:
        pass

def _geiger_loop():
    while True:
        path = geiger_path()
        if path and hunting() and HUNT.get("live") and not HUNT["found"] and not MUTED and not intro_playing():
            close = HUNT.get("close", 0.0)
            _play_geiger_tick(path, close)
            mean = GEIGER_SLOWEST - (GEIGER_SLOWEST - GEIGER_FASTEST) * close
            time.sleep(min(mean * 2.5, max(0.06, random.expovariate(1.0 / mean))))
        else:
            time.sleep(0.1)

def ensure_geiger_thread():
    if GEIGER["thread"] is None and geiger_path():
        GEIGER["thread"] = threading.Thread(target=_geiger_loop, daemon=True, name="geiger")
        GEIGER["thread"].start()

# =============================================================================
# IDENTIFICATION DATA & FALLBACKS
# =============================================================================
COMPANY_FALLBACK = {
    0x0000: "Ericsson", 0x0001: "Nokia", 0x0002: "Intel", 0x0006: "Microsoft", 0x0008: "Motorola",
    0x000A: "Qualcomm (CSR)", 0x000D: "Texas Instruments", 0x000F: "Broadcom", 0x001D: "Qualcomm",
    0x0030: "STMicroelectronics", 0x0046: "MediaTek", 0x004C: "Apple", 0x0057: "Harman International",
    0x0059: "Nordic Semiconductor", 0x005D: "Realtek", 0x0075: "Samsung Electronics", 0x0078: "Nike",
    0x0087: "Garmin", 0x009E: "Bose", 0x00C4: "LG Electronics", 0x00E0: "Google", 0x012D: "Sony",
    0x0131: "Cypress Semiconductor", 0x0157: "Huami (Amazfit/Zepp)", 0x0171: "Amazon", 0x027D: "Huawei",
    0x02E5: "Espressif", 0x038F: "Xiaomi", 0x0499: "Ruuvi Innovations", 0x067C: "Tile",
}

SERVICE_RULES = {
    "FEAA": ("smart_iot", "Eddystone beacon", 75), "FEED": ("trackers_valuables", "Tile tracker", 80),
    "FD84": ("trackers_valuables", "Tile tracker", 80), "FD5A": ("trackers_valuables", "Samsung SmartTag", 80),
    "FD6F": ("smartphones", "Phone (Exposure Notification)", 70),
    "FE2C": ("wearables_audio", "Google Fast Pair accessory", 70), "FE07": ("wearables_audio", "Sonos", 75),
    "FEBE": ("wearables_audio", "Bose", 75), "FE1F": ("wearables_audio", "Garmin device", 75),
    "FEE0": ("wearables_audio", "Huami/Amazfit band", 75), "FEE1": ("wearables_audio", "Huami/Amazfit band", 75),
    "FE0F": ("smart_iot", "Philips Hue / Signify", 75), "FEFD": ("smart_iot", "Gimbal beacon", 70),
    "FEFE": ("medical_health", "GN hearing device", 70), "FE59": ("smart_iot", "Nordic DFU (firmware mode)", 60),
    "180D": ("wearables_audio", "Heart-rate sensor", 65), "1810": ("medical_health", "Blood-pressure monitor", 70),
    "1808": ("medical_health", "Glucose meter", 70), "181F": ("medical_health", "Continuous glucose monitor", 70),
    "183A": ("medical_health", "Insulin delivery", 70), "1809": ("medical_health", "Thermometer", 70),
    "1822": ("medical_health", "Pulse oximeter", 70), "181D": ("medical_health", "Weight scale", 65),
    "1812": ("other", "HID (keyboard/mouse/gamepad)", 55), "1826": ("wearables_audio", "Fitness machine", 60),
    "1816": ("wearables_audio", "Cycling sensor", 60), "1814": ("wearables_audio", "Running sensor", 60),
    "1818": ("wearables_audio", "Cycling power meter", 60), "181A": ("smart_iot", "Environmental sensor", 60),
    "1827": ("smart_iot", "Bluetooth Mesh node", 60), "1828": ("smart_iot", "Bluetooth Mesh node", 60),
    "FFFA": ("auto_aerial", "Drone Remote ID (ASTM F3411)", 80),
}
RAVEN_UUIDS = {"3100", "3200", "3300", "3400", "3500"}   # Raven BLE services (community research)

APPLE_TYPES = {
    0x07: ("wearables_audio", "AirPods / Beats (proximity pairing)"), 0x12: ("trackers_valuables", "Apple Find My beacon (AirTag / accessory)"),
    0x02: ("smart_iot", "iBeacon"), 0x06: ("smart_iot", "HomeKit accessory"),
    0x09: ("wearables_audio", "AirPlay target (Apple TV / HomePod)"), 0x0A: ("smartphones", "Apple device (AirPlay source)"),
}
APPLE_PRIORITY = [0x07, 0x12, 0x02, 0x06, 0x09, 0x0A]

MS_CDP = {
    1: ("handhelds_gaming", "Xbox One"), 6: ("smartphones", "iPhone (via Windows CDP)"), 7: ("laptops_tablets", "iPad (via Windows CDP)"),
    8: ("smartphones", "Android device (via Windows CDP)"), 9: ("laptops_tablets", "Windows desktop"),
}

APPEARANCE = {
    1: ("smartphones", "Phone"), 2: ("laptops_tablets", "Computer"), 3: ("wearables_audio", "Watch"),
    8: ("trackers_valuables", "Tag"), 9: ("trackers_valuables", "Key ring"), 13: ("wearables_audio", "Heart-rate sensor"),
}

BLUEZ_ICONS = {
    "phone": ("smartphones", "Phone"), "computer": ("laptops_tablets", "Computer"),
    "audio-headset": ("wearables_audio", "Headset"), "audio-headphones": ("wearables_audio", "Headphones"),
    "input-gaming": ("handhelds_gaming", "Game controller"),
}

VENDOR_FALLBACK = [(re.compile(p, re.I), c) for p, c in [
    (r"\btile\b", "trackers_valuables"), (r"ledger", "trackers_valuables"),
    (r"ruuvi|espressif|nordic|tuya|govee|switchbot|aqara", "smart_iot"),
    (r"garmin|huami|bose|harman|jabra|polar|suunto|fitbit|whoop|oura", "wearables_audio"),
    (r"dexcom|medtronic|resmed|omron|abbott", "medical_health"),
    (r"tesla|rivian|lucid|polestar|bmw|audi|mercedes|porsche|ford|toyota|honda", "auto_aerial"),
    (r"apple|samsung|google|xiaomi|huawei|oneplus", "smartphones"),
    (r"microsoft|lenovo|dell|asus|acer", "laptops_tablets"),
    (r"sony|nintendo|valve|razer", "handhelds_gaming"),
]]

CATEGORY_TERMS = [
    ("hacker_pentest", [
        r"flipper(?: zero)?", r"wifi pineapple", r"hackrf", r"portapack", r"proxmark", r"ubertooth",
        r"pwnagotchi", r"esp32-marauder", r"marauder", r"rubber ducky", r"hak5", r"packet squirrel",
        r"nrf ?sniffer", r"cardputer", r"m5(?:stack|stick|core)\w*", r"chameleon ?(?:ultra|mini)"
    ]),
    ("medical_health", [
        r"dexcom(?: g\d)?", r"freestyle", r"libre ?\d?", r"omron", r"glucometer", r"pulse oximeter",
        r"cpap", r"resmed", r"airsense", r"medtronic", r"insulin", r"cgm", r"hearing aid", r"phonak", r"oticon"
    ]),
    ("wearables_audio", [
        r"apple watch", r"airpods\w*", r"beats(?: \w+)?", r"galaxy (?:watch|buds|fit|ring)\w*",
        r"pixel (?:watch|buds)\w*", r"fitbit", r"garmin", r"amazfit", r"zepp", r"whoop", r"polar\w*",
        r"oura", r"wh-1000x\w*", r"wf-1000x\w*", r"bose", r"quietcomfort", r"jabra", r"sennheiser",
        r"jbl", r"soundcore", r"sonos", r"echo \w*", r"homepod", r"smart ?tv"
    ]),
    ("handhelds_gaming", [
        r"steam ?deck", r"rog ally", r"playstation portal", r"dualsense", r"dualshock", r"wireless controller",
        r"xbox\w*", r"pro controller", r"joy-?con\w*", r"nintendo switch", r"meta quest", r"oculus",
        r"apple vision pro", r"xreal", r"ray-?ban meta", r"8bitdo\w*"
    ]),
    ("trackers_valuables", [
        r"airtag", r"tile", r"smart ?tag\w*", r"chipolo", r"pebblebee", r"find ?my", r"tracker",
        r"ledger", r"trezor", r"coldcard", r"tangem", r"hardware wallet", r"tractive", r"smart collar"
    ]),
    ("smartphones", [
        r"iphone", r"galaxy (?:s|z|a|m|note)\s?\d+\w*", r"sm-[gsanfme]\d{3}\w*", r"pixel \d+\w*",
        r"oneplus", r"xiaomi", r"redmi\w*", r"poco \w+", r"huawei", r"honor", r"moto\w*", r"oppo", r"vivo"
    ]),
    ("laptops_tablets", [
        r"macbook", r"thinkpad", r"surface \w*", r"chromebook", r"latitude", r"xps ?\d*", r"ipad", r"galaxy tab\w*"
    ]),
    ("auto_aerial", [
        r"tesla", r"rivian", r"lucid", r"polestar", r"bmw", r"audi", r"mercedes", r"porsche", r"ford",
        r"chevrolet", r"toyota", r"honda", r"key ?fob", r"smart key", r"obd\w*", r"elm327", r"tpms",
        r"dash ?cam", r"dji", r"mavic", r"matrice", r"autel", r"skydio", r"fpv", r"drone"
    ]),
    ("smart_iot", [
        r"august", r"schlage", r"yale", r"ring \w*", r"arlo", r"hue", r"nest", r"thermostat", r"smart lock",
        r"ecobee", r"blink", r"eufy", r"wyze", r"smartthings", r"home assistant", r"esphome", r"govee",
        r"switchbot", r"shelly\w*", r"sonoff", r"tuya", r"aqara", r"philips hue", r"esp32\w*", r"arduino", r"beacon"
    ]),
]
CATEGORY_RX = [(cat, build_rx(terms)) for cat, terms in CATEGORY_TERMS]
TESLA_NAME = re.compile(r"^s[0-9a-f]{16}c$")

ALERT_STRONG_NAMES = build_rx([
    r"(?<!zte )axon[ -](?:body|flex|fleet|signal|dock|evidence|capture|respond)\w*", r"taser\w*", r"body-?worn", r"bodycam", r"evidence\.com",
    r"watchguard", r"digital ally", r"whelen", r"federal signal", r"flock safety", r"autovu", r"genetec",
    r"alpr", r"flock-[a-z0-9]{4,}", r"fs ext battery", r"pigvision", r"stalker \w*", r"kustom signals", r"decatur\w*", r"speed ?cam", r"l3harris", r"anduril", r"aerovironment"
])
ALERT_FORCE_NAMES = build_rx([r"dji", r"mavic", r"matrice", r"phantom \d", r"autel", r"skydio", r"parrot"])
ALERT_SOFT_NAMES = build_rx([r"motorola solutions", r"mototrbo", r"apx", r"cradlepoint", r"sierra wireless", r"flir"])

ORG_STRONG = re.compile(r"\b(axon enterprise|taser|watchguard video|digital ally|flock safety|applied concepts|kustom signals|decatur electronics|"
                        r"whelen|federal signal|persistent systems|anduril|aerovironment|shield ai|skydio|autel|dji|parrot)\b", re.I)
ORG_POSSIBLE = re.compile(r"(motorola solutions|l3harris|harris corp|genetec|flir|cradlepoint|sierra wireless)", re.I)
SEED_OUIS = {"60:60:1F": "DJI", "00:25:DF": "Axon / TASER International"}

CATEGORIES = [
    ("smartphones", "📱", "SMARTPHONES", "cyan"), ("laptops_tablets", "💻", "LAPTOPS & TABLETS", "blue"),
    ("handhelds_gaming", "🎮", "HANDHELDS · GAMING · XR", "magenta"), ("wearables_audio", "🎧", "WEARABLES · AUDIO · MEDIA", "bright_cyan"),
    ("hacker_pentest", "⚡", "HACKER & PENTEST GEAR", "red"), ("auto_aerial", "🚗", "AUTO · MOTO · AERIAL", "yellow"),
    ("smart_iot", "🏠", "SMART HOME & IOT", "green"), ("trackers_valuables", "📍", "TRACKERS & VALUABLES", "white"),
    ("medical_health", "🩺", "MEDICAL & HEALTH", "bright_magenta"), ("networking_mesh", "🌐", "NETWORKING & MESH", "bright_blue"), ("proximity_beacons", "📡", "PROXIMITY BEACONS", "bright_green"),
    ("industrial_logistics", "🏭", "INDUSTRIAL & LOGISTICS", "orange3"), ("fitness_gym", "🏋", "FITNESS & GYM", "bright_yellow"),
    ("pet_trackers", "🐾", "PET TRACKERS", "pink1"), ("smart_appliances", "🧺", "SMART APPLIANCES", "spring_green3"),
    ("other", "🔌", "OTHER / UNCLASSIFIED", "grey62"),
    ("anonymous", "👻", "HIDDEN / ANONYMOUS", "grey42"),
]
CATEGORY_ICONS = {c[0]: c[1] for c in CATEGORIES}
CATEGORY_COLORS = {c[0]: c[3] for c in CATEGORIES}
CIVILIAN = {"smartphones", "laptops_tablets", "wearables_audio", "smart_iot", "smart_appliances", "fitness_gym", "pet_trackers", "other", "anonymous"}
# Categories the Security Watch view always surfaces (alert/possible tactical devices, follower alerts and
# flagged known devices are included regardless). Extend via "security_categories" in scanner_config.json.
SECURITY_CATS = {"hacker_pentest", "trackers_valuables", "auto_aerial"}

OUI_SOURCES = {
    "oui.csv": "https://standards-oui.ieee.org/oui/oui.csv",
    "mam.csv": "https://standards-oui.ieee.org/oui28/mam.csv",
    "oui36.csv": "https://standards-oui.ieee.org/oui36/oui36.csv",
}
SIG_SOURCES = {
    "company_ids.json": "https://raw.githubusercontent.com/NordicSemiconductor/bluetooth-numbers-database/master/v1/company_ids.json",
    "service_uuids.json": "https://raw.githubusercontent.com/NordicSemiconductor/bluetooth-numbers-database/master/v1/service_uuids.json",
}

# =============================================================================
# REGISTRY & IDENTIFICATION
# =============================================================================
class Registry:
    def __init__(self):
        self.company = dict(COMPANY_FALLBACK)
        self.services: dict[str, str] = {}
        self.oui: dict[str, str] = {}
        self.sig_source = "built-in (small)"
        self.config_company: dict[int, str] = {}

    def load_all(self, extra_oui: str | None = None):
        cj = CACHE_DIR / "company_ids.json"
        try:
            if cj.exists():
                for e in json.loads(cj.read_text(encoding="utf-8")):
                    self.company[int(e["code"])] = str(e["name"])
                self.sig_source = "SIG (cached)"
        except Exception:
            pass
        if self.sig_source.startswith("built-in"):
            try:
                import bluetooth_numbers as bn
                for k, v in bn.company.items():
                    self.company[int(k)] = str(v)
                self.sig_source = "bluetooth-numbers pkg"
            except Exception:
                pass
        try:
            sj = CACHE_DIR / "service_uuids.json"
            if sj.exists():
                for e in json.loads(sj.read_text(encoding="utf-8")):
                    self.services[str(e["uuid"]).upper().replace("0X", "")[-4:]] = str(e["name"])
        except Exception:
            pass
        paths = [CACHE_DIR / n for n in OUI_SOURCES] + ([Path(extra_oui)] if extra_oui else [])
        for p in paths:
            try:
                if p.exists():
                    with open(p, newline="", encoding="utf-8", errors="replace") as f:
                        rd = csv.reader(f)
                        next(rd, None)
                        for row in rd:
                            if len(row) >= 3 and row[1]:
                                self.oui[row[1].strip().upper()] = row[2].strip()
            except Exception:
                pass

    def company_name(self, cid: int) -> str:
        return self.company.get(cid, "") or self.config_company.get(cid, "")

    def oui_org(self, mac: str) -> str:
        h = mac.replace(":", "").upper()
        for n in (9, 7, 6):
            org = self.oui.get(h[:n])
            if org:
                return org
        return ""

    def uuid_name(self, short: str) -> str:
        if short in SERVICE_RULES:
            return SERVICE_RULES[short][1]
        if short in self.services:
            return self.services[short]
        return ""

REG = Registry()

# -----------------------------------------------------------------------------
# scanner_config.json: company IDs, OUIs, name -> category terms, custom names, ignore list
# -----------------------------------------------------------------------------
CONFIG: dict = {}
CFG_NAMES: dict[str, str] = {}        # MAC -> display name
CFG_IGNORE: set = set()               # MACs never shown
CFG_IGNORE_NAMES: list = []           # advertised-name patterns never shown (config "ignore_names")
CFG_OUI: dict[str, tuple] = {}        # "AA:BB:CC" -> (label, "alert" | "possible" | "info:<category>")
CFG_TERM_CAT: dict[str, str] = {}     # normalised term -> scanner category
CFG_TERM_RX = None
CFG_TACTICAL: dict[str, str] = {"law_enforcement_tactical": "alert"}   # category -> "alert" | "possible" (shown in the tactical panel)
CFG_CAT_MAP = {"audio_wearables": "wearables_audio"}                  # alias -> real category (extend via config "category_aliases")
CFG_REGEX: list = []                  # (category, compiled regex) from config "category_regex"
CFG_VENDOR: list = []                 # (category, compiled regex) from config "vendor_categories": matched against the vendor / company name
CFG_ALERT_RX = None                   # config "alert_names"
CFG_POSSIBLE_RX = None                # config "possible_names"
CFG_WARNINGS: list[str] = []
RESERVED_CATS = {"tactical", "other", "anonymous"}
CAT_PALETTE = ["bright_red", "dark_orange", "gold1", "chartreuse2", "turquoise2", "deep_sky_blue1",
               "medium_purple1", "hot_pink", "light_salmon1", "khaki1", "aquamarine1", "orchid1"]
CFG_NEW_CATS: list[str] = []

def _valid_style(style: str) -> bool:
    if not HAVE_RICH:
        return True
    try:
        from rich.style import Style
        Style.parse(style)
        return True
    except Exception:
        return False

def register_category(key, icon=None, title=None, color=None, civilian=None):
    """Add a dashboard category at runtime, or restyle an existing one. Nothing in the scanner is keyed to a fixed list."""
    if color and not _valid_style(color):
        CFG_WARNINGS.append(f"category '{key}': unknown colour '{color}' (ignored)")
        color = None
    for i, c in enumerate(CATEGORIES):
        if c[0] == key:
            CATEGORIES[i] = (key, icon or c[1], title or c[2], color or c[3])
            break
    else:
        pos = next((i for i, c in enumerate(CATEGORIES) if c[0] == "other"), len(CATEGORIES))
        color = color or CAT_PALETTE[len(CFG_NEW_CATS) % len(CAT_PALETTE)]
        CATEGORIES.insert(pos, (key, icon or "🔹", title or key.replace("_", " ").upper(), color))
        CFG_NEW_CATS.append(key)
    c = next(c for c in CATEGORIES if c[0] == key)
    CATEGORY_ICONS[key], CATEGORY_COLORS[key] = c[1], c[3]
    if civilian is True:
        CIVILIAN.add(key)
    elif civilian is False:
        CIVILIAN.discard(key)

def ensure_category(cat: str):
    """Config category name -> real category key, creating a dashboard panel for names the scanner has never seen."""
    mapped = CFG_CAT_MAP.get(cat, cat)
    if mapped in {c[0] for c in CATEGORIES}:
        return mapped
    if not re.fullmatch(r"[a-z0-9_]{1,40}", mapped):
        CFG_WARNINGS.append(f"category '{cat}': name must be lowercase letters/digits/underscore (sent to 'other')")
        return "other"
    register_category(mapped)
    return mapped

def _compile_name_rules(items, label):
    """Plain strings are matched as whole words; 're:<pattern>' is a raw regex."""
    parts = []
    for t in items or []:
        t = str(t)
        if t.lower().startswith("re:"):
            pat = t[3:]
            try:
                re.compile(pat)
                parts.append(pat)
            except re.error as e:
                CFG_WARNINGS.append(f"{label}: bad regex '{pat}': {e}")
        elif norm(t):
            parts.append(re.escape(norm(t)))
    return build_rx(parts) if parts else None

def find_config(path):
    for p in (Path(path), Path(__file__).resolve().parent / Path(path).name):
        if p.exists():
            return p
    return None

def load_config(path=CONFIG_FILE) -> str:
    global CONFIG, CFG_TERM_RX
    p = find_config(path)
    if not p:
        return f"{path} not found (built-in rules only)"
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except Exception as e:
        return f"{p.name} unreadable: {e}"
    CONFIG = data
    for k, v in (data.get("company_ids") or {}).items():
        try:
            REG.config_company[int(str(k), 0)] = str(v)
        except ValueError:
            pass
    conf = data.get("oui_confidence") or {}
    for pre, label in (data.get("target_ouis") or {}).items():
        CFG_OUI[pre.upper()] = (str(label), str(conf.get(pre, conf.get(pre.upper(), "possible"))))
    CFG_NAMES.update({k.upper(): str(v) for k, v in (data.get("custom_names") or {}).items()})
    CFG_IGNORE.update(str(m).upper() for m in (data.get("ignore_list") or []))
    CFG_IGNORE_NAMES.extend(s for s in (str(n).strip() for n in (data.get("ignore_names") or [])) if s and s not in CFG_IGNORE_NAMES)

    # ---- categories: everything here is optional and driven by the config -----------------------------
    CFG_CAT_MAP.update({str(k): str(v) for k, v in (data.get("category_aliases") or {}).items()})
    for cat in data.get("tactical_categories") or []:
        CFG_TACTICAL.setdefault(str(cat), "alert")
    meta = data.get("category_meta") or {}
    for key, m in meta.items():
        if not isinstance(m, dict):
            continue
        if m.get("tier") in ("alert", "possible"):            # tier => lives in the tactical panel, not its own panel
            CFG_TACTICAL[key] = m["tier"]
            continue
        if key in CFG_TACTICAL or key in RESERVED_CATS or key in CFG_CAT_MAP:
            if key in RESERVED_CATS and any(m.get(f) for f in ("icon", "title", "color")):
                register_category(key, m.get("icon"), m.get("title"), m.get("color"), m.get("civilian"))
            continue
        if not re.fullmatch(r"[a-z0-9_]{1,40}", key):
            CFG_WARNINGS.append(f"category_meta '{key}': invalid name (use lowercase letters, digits, underscore)")
            continue
        register_category(key, m.get("icon"), m.get("title"), m.get("color"), m.get("civilian"))
    for cat, terms in (data.get("categories") or {}).items():
        if cat in CFG_TACTICAL:
            mapped = cat
        else:
            mapped = ensure_category(str(cat))
        for t in terms or []:
            nt = norm(str(t))
            if nt and nt not in CFG_TERM_CAT:
                CFG_TERM_CAT[nt] = mapped
    for cat, pats in (data.get("category_regex") or {}).items():
        mapped = cat if cat in CFG_TACTICAL else ensure_category(str(cat))
        for pat in pats or []:
            try:
                CFG_REGEX.append((mapped, re.compile(str(pat), re.I)))
            except re.error as e:
                CFG_WARNINGS.append(f"category_regex '{cat}': bad regex '{pat}': {e}")
    for k, v in (data.get("service_rules") or {}).items():      # {"FEAA": ["smart_iot", "Eddystone beacon", 75]}
        try:
            cat, label, conf_ = (v["category"], v["label"], v.get("confidence", 65)) if isinstance(v, dict) else (v[0], v[1], v[2] if len(v) > 2 else 65)
            SERVICE_RULES[str(k).upper().replace("0X", "")] = (ensure_category(str(cat)), str(label), int(conf_))
        except Exception:
            CFG_WARNINGS.append(f"service_rules '{k}': expected [category, label, confidence]")
    for cat, terms in (data.get("vendor_categories") or {}).items():     # {"smart_iot": ["govee", "re:^telink"]}: a vendor (SIG company or IEEE OUI owner) -> category
        if cat in CFG_TACTICAL:
            CFG_WARNINGS.append(f"vendor_categories '{cat}': tactical categories can't be set from a vendor name (use target_ouis); skipped")
            continue
        rx = _compile_name_rules(terms, f"vendor_categories '{cat}'")
        if rx:
            CFG_VENDOR.append((ensure_category(str(cat)), rx))
    for cat in data.get("security_categories") or []:
        SECURITY_CATS.add(ensure_category(str(cat)))
    global CFG_ALERT_RX, CFG_POSSIBLE_RX
    CFG_ALERT_RX = _compile_name_rules(data.get("alert_names"), "alert_names")
    CFG_POSSIBLE_RX = _compile_name_rules(data.get("possible_names"), "possible_names")
    if CFG_TERM_CAT:
        CFG_TERM_RX = build_rx([re.escape(t) for t in sorted(CFG_TERM_CAT, key=len, reverse=True)])
    extra = f", {len(CFG_NEW_CATS)} new categories" if CFG_NEW_CATS else ""
    return (f"{p.name}: {len(CFG_TERM_CAT)} name terms, {len(CFG_REGEX)} regex rules, {len(CFG_OUI)} OUIs, "
            f"{len(REG.config_company)} company IDs{extra}")

def classify_config_name(nn: str):
    """Longest config term (plain or regex) found in the normalised name -> (category, term)."""
    if not nn:
        return None, None
    best, best_cat = None, None
    if CFG_TERM_RX:
        for m in CFG_TERM_RX.finditer(nn):
            if best is None or len(m.group(0)) > len(best):
                best, best_cat = m.group(0), CFG_TERM_CAT.get(m.group(0))
    for cat, rx in CFG_REGEX:
        m = rx.search(nn)
        if m and m.group(0) and (best is None or len(m.group(0)) > len(best)):
            best, best_cat = m.group(0), cat
    return (best_cat, best) if best else (None, None)

def update_db():
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    ok = 0
    for fn, url in {**OUI_SOURCES, **SIG_SOURCES}.items():
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (signal-ops-irl)"})
            data = urllib.request.urlopen(req, timeout=90).read()
            (CACHE_DIR / fn).write_bytes(data)
            print(f"  ✓ {fn}  ({len(data) // 1024} KB)")
            ok += 1
        except Exception as e:
            print(f"  ✗ {fn}: {e}")
    print(f"Updated {ok}/{len(OUI_SOURCES) + len(SIG_SOURCES)} databases in {CACHE_DIR}")

@dataclass
class Identity:
    category: str = "other"
    label: str = ""
    vendor: str = ""
    tier: str = ""
    confidence: int = 0
    reasons: list = field(default_factory=list)
    addr_type: str = "unknown"
    known: str = ""
    known_alert: bool = False

def apple_types(data: bytes):
    i, out = 0, []
    while i + 1 < len(data):
        out.append(data[i])
        i += 2 + data[i + 1]
    return out

def classify_name(nn: str):
    for cat, rx in CATEGORY_RX:
        m = rx.search(nn)
        if m:
            return cat, m.group(0)
    return None, None

def identify(mac, name, mfg, uuids, props, kind, known=None) -> Identity:
    nn = norm(name)
    cnames = [n for n in (REG.company_name(c) for c in mfg) if n]
    org = REG.oui_org(mac) if kind == "public" else ""
    ident = Identity(addr_type=kind, vendor=(cnames[0] if cnames else org))

    def tactical(tier, label, reason, conf):
        ident.category, ident.tier, ident.label, ident.confidence = "tactical", tier, label, conf
        ident.reasons = [reason]
        return ident

    org_possible = None
    oui_info = None
    if kind in ("public", "random", "unknown") and MAC_RE.match(mac):    # Windows/macOS report no address type
        hit = CFG_OUI.get(mac[:8])
        if hit:
            label, mode = hit
            if mode == "alert":
                return finish_known(tactical("alert", label, f"config OUI {mac[:8]}", 85), known, mac, name, mfg, uuids, kind)
            if mode == "possible":
                org_possible = (label, f"config OUI {mac[:8]} (weak evidence)")
            elif mode.startswith("info:"):
                oui_info = (mode[5:], label, f"config OUI {mac[:8]}")
    for src, text in [("IEEE OUI", org)] + [("SIG company", c) for c in cnames]:
        if text and ORG_STRONG.search(text):
            return finish_known(tactical("alert", text, f"{src}: {text}", 90), known, mac, name, mfg, uuids, kind)
        if text and ORG_POSSIBLE.search(text) and not org_possible:
            org_possible = (text, f"{src}: {text}")
    if RAVEN_UUIDS & set(uuids):
        return finish_known(tactical("alert", "Raven gunshot sensor (BLE services)", "service UUID 0x3100-0x3500", 75), known, mac, name, mfg, uuids, kind)
    cfg_cat, cfg_hit = classify_config_name(nn)
    if cfg_cat in CFG_TACTICAL:
        tier = CFG_TACTICAL[cfg_cat]
        return finish_known(tactical(tier, name or cfg_hit, f"config name ~ '{cfg_hit}'", 75 if tier == "alert" else 62), known, mac, name, mfg, uuids, kind)
    m = CFG_ALERT_RX.search(nn) if CFG_ALERT_RX else None
    if m:
        return finish_known(tactical("alert", name or m.group(0), f"config alert name ~ '{m.group(0)}'", 78), known, mac, name, mfg, uuids, kind)
    m = ALERT_STRONG_NAMES.search(nn)
    if m:
        return finish_known(tactical("alert", name or m.group(0), f"name ~ '{m.group(0)}'", 80), known, mac, name, mfg, uuids, kind)
    m = ALERT_FORCE_NAMES.search(nn)
    if m:
        return finish_known(tactical("possible", name or m.group(0), f"name ~ '{m.group(0)}'", 70), known, mac, name, mfg, uuids, kind)
    m = CFG_POSSIBLE_RX.search(nn) if CFG_POSSIBLE_RX else None
    if m:
        return finish_known(tactical("possible", name or m.group(0), f"config possible name ~ '{m.group(0)}'", 65), known, mac, name, mfg, uuids, kind)
    if 0x09C8 in mfg:
        return finish_known(tactical("possible", "Flock / Raven hardware (XUNTONG 0x09C8)", "mfg ID 0x09C8 (community marker)", 70), known, mac, name, mfg, uuids, kind)
    if org_possible:
        return finish_known(tactical("possible", org_possible[0], org_possible[1], 60), known, mac, name, mfg, uuids, kind)

    cands = []
    if oui_info and CFG_CAT_MAP.get(oui_info[0], oui_info[0]) in {c[0] for c in CATEGORIES}:
        cands.append((60, CFG_CAT_MAP.get(oui_info[0], oui_info[0]), oui_info[1], oui_info[2]))
    if TESLA_NAME.match(nn):
        cands.append((85, "auto_aerial", "Tesla vehicle (BLE phone-key)", "name pattern S<16hex>C"))
    cat, hit = classify_name(nn)
    if cat:
        cands.append((72, cat, hit, f"name ~ '{hit}'"))
    if cfg_cat:                     # a config term at least as specific as the built-in match wins (your config overrides built-ins)
        cands.append((74 if len(cfg_hit) >= len(hit or "") else 66, cfg_cat, cfg_hit, f"config name ~ '{cfg_hit}'"))
    for u in uuids:
        r = SERVICE_RULES.get(u)
        if r:
            cands.append((r[2], r[0], r[1], f"service {u}"))
    if 0x004C in mfg:
        types = apple_types(mfg[0x004C])
        for t in APPLE_PRIORITY:
            if t in types:
                cands.append((68, APPLE_TYPES[t][0], APPLE_TYPES[t][1], f"Apple Continuity 0x{t:02X}"))
                break
    ms = mfg.get(0x0006)
    if ms and len(ms) > 1 and ms[0] == 0x01 and (ms[1] & 0x3F) in MS_CDP:
        c, l = MS_CDP[ms[1] & 0x3F]
        cands.append((70, c, l, "Microsoft CDP beacon"))
    ap = props.get("Appearance")
    if isinstance(ap, int) and (ap >> 6) in APPEARANCE:
        c, l = APPEARANCE[ap >> 6]
        cands.append((55, c, l, f"GAP appearance 0x{ap:04X}"))
    ic = props.get("Icon")
    if ic in BLUEZ_ICONS:
        cands.append((50, BLUEZ_ICONS[ic][0], BLUEZ_ICONS[ic][1], f"BlueZ icon '{ic}'"))
    for text in cnames + ([org] if org else []):          # your config's vendor rules (a little stronger than the built-in vendor list)
        nt = norm(text)
        hit = next(((c, m.group(0)) for c, rx in CFG_VENDOR for m in [rx.search(nt)] if m), None)
        if hit:
            cands.append((34, hit[0], f"{text} device", f"config vendor ~ '{hit[1]}'"))
    for text in cnames + ([org] if org else []):
        for rx, c in VENDOR_FALLBACK:
            if rx.search(text):
                cands.append((30, c, f"{text} device", "vendor only"))
                break
    best = max(cands, key=lambda c: c[0]) if cands else None

    if best:
        ident.confidence, ident.category, ident.label = best[0], best[1], best[2]
        ident.reasons = [c[3] for c in sorted(cands, key=lambda c: -c[0])][:3]
    return finish_known(ident, known, mac, name, mfg, uuids, kind)

def finish_known(ident, known, mac, name, mfg, uuids, kind):
    if known:
        e = known.match(mac, name, set(mfg), set(uuids))
        if e:
            ident.known, ident.known_alert = e["label"], bool(e.get("alert", True))
            ident.tier, ident.confidence = "known", 100
            ident.reasons.insert(0, "matches your known-devices file")
            if e.get("category") and e["category"] != ident.category:
                ident.category = e["category"]
    return ident

# =============================================================================
# KNOWN DEVICES
# =============================================================================
class KnownDevices:
    def __init__(self, path):
        self.path = path
        self.entries = []
        self.renames: dict[str, str] = {}
        self.ignored: set[str] = set()
        self.ignored_names: list[str] = []       # name patterns hidden permanently (key i)
        self.trusted: set[str] = set()           # trackers you've marked as yours (exempt from follower alerts)
        self.seen: dict = {}
        try:
            data = json.load(open(path))
            self.entries = data.get("devices", [])
            self.renames = data.get("renames", {})
            self.ignored = set(data.get("ignored", []))
            self.ignored_names = [str(n) for n in data.get("ignored_names", []) if str(n).strip()]
            self.trusted = set(data.get("trusted", []))
        except Exception:
            pass

    def match(self, mac, name, mfg_ids, uuids):
        for e in self.entries:
            conds = []
            if "mac" in e:
                macs = e["mac"] if isinstance(e["mac"], list) else [e["mac"]]
                conds.append(mac in [m.upper() for m in macs])
            if "name" in e:
                conds.append(bool(name) and fnmatch.fnmatch(name.lower(), str(e["name"]).lower()))
            if "mfg_id" in e:
                try:
                    conds.append(int(str(e["mfg_id"]), 0) in mfg_ids)
                except ValueError:
                    conds.append(False)
            if "uuid" in e:
                conds.append(str(e["uuid"]).upper() in uuids)
            if conds and all(conds):
                return e
        return None

    def add(self, dev, label, alert=True):
        e = {"label": label, "alert": alert}
        if dev.kind in ("public", "static-random"):
            e["mac"] = dev.mac
        if dev.name:
            e["name"] = glob.escape(dev.name)
        self.entries.append(e)
        self.save()
        return e

    def save(self):
        tmp = self.path + ".tmp"
        try:
            with open(tmp, "w") as f:
                json.dump({
                    "devices": self.entries,
                    "renames": self.renames,
                    "ignored": list(self.ignored),
                    "ignored_names": self.ignored_names,
                    "trusted": sorted(self.trusted),
                }, f, indent=2)
            os.replace(tmp, self.path)                       # atomic: a crash can't leave a truncated registry
        except Exception as e:
            try:
                os.remove(tmp)
            except OSError:
                pass
            log_event(f"known-devices save failed: {e}", "error")

KNOWN: KnownDevices | None = None

STATUS = type("Status", (), {"text": "", "t": 0.0, "set": lambda self, t: setattr(self, "text", t) or setattr(self, "t", time.time())})()

# -----------------------------------------------------------------------------
# Scan-time tracking
# -----------------------------------------------------------------------------
SESSION = {"scan_seconds": 0.0, "start": None}   # scan time this run; start = wall-clock start (set in main)
EVENTS: list = []                           # (timestamp, level, text) notable moments, shown in the session report
EVENT_FLAGGED: set = set()                  # MACs already logged as alert / possible
ARCHIVED_GHOSTS: list = []                  # ghost clusters pruned mid-session, kept for the report

def log_event(text: str, level: str = "info"):
    if len(EVENTS) < 1000:
        EVENTS.append((time.time(), level, clean(text, 200)))
TICK = {"last": None}
MAX_TICK = 2.0                              # a longer gap means the UI was blocked (prompt); don't count it

def fmt_dur(sec, compact=False) -> str:
    s = max(0, int(sec))
    h, rem = divmod(s, 3600)
    m, sc = divmod(rem, 60)
    if compact:
        if h:
            return f"{h}h" + (f" {m}m" if m else "")
        if m:
            return f"{m}m" + (f" {sc}s" if sc else "")
        return f"{sc}s"
    if h:
        return f"{h}h {m:02d}m"
    if m:
        return f"{m}m {sc:02d}s"
    return f"{sc}s"

def tick_scan_time(now: float, scanning: bool) -> float:
    """Add the time since the last tick to this session's scan time, but only while actually scanning."""
    last, TICK["last"] = TICK["last"], now
    if last is None or not scanning:
        return 0.0
    dt = min(max(0.0, now - last), MAX_TICK)
    if dt <= 0:
        return 0.0
    SESSION["scan_seconds"] += dt
    return dt

def reset_tick():
    """Call after anything that blocks the main loop (input prompts) so that gap isn't counted."""
    TICK["last"] = None

# -----------------------------------------------------------------------------
# Hunt mode (hot / cold locator)
# -----------------------------------------------------------------------------
HUNT = {"mac": None, "start": 0.0, "start_rssi": None, "best": -127.0, "hot_since": None, "found": False, "next_beep": 0.0,
        "next_ping": 0.0, "pings": collections.deque(maxlen=4), "close": 0.0}
HUNT_FOUND_RSSI = -55                       # about arm's length
HUNT_HOLD = 3.0                             # seconds you must stay that close

def hunting() -> bool:
    return HUNT["mac"] is not None

def start_hunt(mac: str):
    dev = DEVICES.get(mac)
    HUNT.update(mac=mac, start=time.time(), start_rssi=(dev.ema if dev else None), best=-127.0,
                hot_since=None, found=False, next_beep=0.0, next_ping=0.0, close=0.0, live=False)
    HUNT["pings"].clear()
    ensure_geiger_thread()
    game_on_hunt(False)

def stop_hunt():
    HUNT.update(mac=None, start_rssi=None, hot_since=None, found=False, next_ping=0.0, close=0.0, live=False)
    HUNT["pings"].clear()
    CFG["show_hunt"] = False

def fast_rssi(dev, now: float, lo: float = 0.0, hi: float = 1.5):
    """Mean RSSI of samples between lo and hi seconds ago (quicker to react than dev.ema)."""
    vals = [r for t, r in dev.hist if lo <= now - t <= hi]
    return sum(vals) / len(vals) if vals else None

def hunt_temp(r: float):
    for floor, label, col in ((-50, "BURNING HOT", "bright_red"), (-60, "HOT", "red"), (-70, "WARM", "yellow"),
                              (-80, "COOL", "cyan"), (-90, "COLD", "blue")):
        if r >= floor:
            return label, col
    return "ICE COLD", "bright_blue"

def hunt_trend(dev, now: float):
    recent, before = fast_rssi(dev, now, 0, 2.0), fast_rssi(dev, now, 2.0, 6.0)
    if recent is None or before is None:
        return "…", "dim"
    d = recent - before
    return ("▲ warmer", "green") if d > 1.5 else ("▼ colder", "red") if d < -1.5 else ("● steady", "dim")

def hunt_tick(now: float):
    if not hunting():
        return
    dev = DEVICES.get(HUNT["mac"])
    if dev is None or now - dev.last > 3.0:
        HUNT["hot_since"] = None
        HUNT["live"] = False                              # signal lost: the Geiger ticks go quiet
        return
    HUNT["live"] = True
    r = fast_rssi(dev, now) or dev.ema
    if HUNT["start_rssi"] is None:
        HUNT["start_rssi"] = r
    HUNT["best"] = max(HUNT["best"], r)
    close = max(0.0, min(1.0, (r + 95) / 45))
    HUNT["close"] = close
    if now >= HUNT["next_ping"]:                      # one clock drives both the sonar ring and the Geiger-style beep
        HUNT["next_ping"] = now + 2.0 - 1.8 * close   # faster as you get closer
        HUNT["pings"].append(now)
        if not HUNT["found"] and not MUTED and not intro_playing() and not geiger_path():
            sys.stdout.write("\a")
            sys.stdout.flush()
    if HUNT["found"]:
        return
    if r >= HUNT_FOUND_RSSI:
        HUNT["hot_since"] = HUNT["hot_since"] or now
        if now - HUNT["hot_since"] >= HUNT_HOLD:
            complete_hunt(dev, now)
    else:
        HUNT["hot_since"] = None

def complete_hunt(dev, now: float):
    HUNT["found"] = True
    took = fmt_dur(now - HUNT["start"])
    name = clean(dev.name or dev.ident.label or dev.mac, 30)
    log_event(f"Hunt: target located, {name} ({dev.mac}) in {took}", "hunt")
    game_on_hunt(True)
    STATUS.set(f"🎯 TARGET LOCATED: {name} in {took}")
    play_notification_sound()

# -----------------------------------------------------------------------------
# Follower detection
#
# Looks for trackers (AirTag / Tile / SmartTag...) that stay close to YOU across different places.
# There is no GPS, so "place" is inferred: every 20 s we take the set of fixed-address devices
# around you (TVs, cars, wearables...) and treat a lasting change of that set as having moved.
# A tracker that is strongly present through 2-3 such places is flagged. Limits: a tracker whose
# address rotates is only followed while one address lasts (AirTags away from their owner keep
# one for ~24 h), and where few fixed devices are around, movement can't be seen.
# -----------------------------------------------------------------------------
FOLLOW = {
    "scope": "trackers",        # "trackers" or "all" (--follow-all: any fixed-address device too; noisier)
    "near_rssi": -80,           # smoothed RSSI that counts as "near you"
    "present": 10.0,            # seen within this many seconds to count as present
    "min_loc_s": 60.0,          # near-time needed in a place before the place counts
    "watch_s": 900.0,           # close for 15 min (movement unknown)        -> WATCH
    "suspect_s": 600.0,         # 2 places and 10 min close                  -> SUSPECT
    "alert_s": 900.0,           # 3 places and 15 min close                  -> ALERT
    "scene_every": 20.0,        # seconds between surroundings snapshots
    "overlap": 0.25,            # share of current surroundings that must match a place to be "there"
    "ambient_min": 3,           # need this many fixed devices around to judge location
}
FOLLOW_RANK = {"": 0, "watch": 1, "suspect": 2, "alert": 3}

@dataclass
class Tail:
    mac: str
    first: float
    last: float
    label: str = ""
    near_s: float = 0.0
    locs: dict = field(default_factory=dict)        # place id -> seconds near you there (-1 = place unknown)
    tier: str = ""
    flagged: bool = False

TAILS: dict[str, Tail] = {}
SCENE = {"locs": [], "cur": None, "pending": None, "pending_n": 0, "last": 0.0}

def follow_eligible(dev) -> bool:
    if KNOWN and (dev.mac in KNOWN.trusted or dev.ident.known):
        return False
    if dev.ident.category == "trackers_valuables":
        return True
    return FOLLOW["scope"] == "all" and dev.kind in ("public", "static-random")

def ambient_set(now: float) -> set:
    return {d.mac for d in DEVICES.values()
            if d.kind in ("public", "static-random") and now - d.last <= 60 and d.ema >= -95
            and d.mac not in TAILS and d.ident.category != "trackers_valuables"}

def scene_tick(now: float):
    sc = SCENE
    if now - sc["last"] < FOLLOW["scene_every"]:
        return
    sc["last"] = now
    amb = ambient_set(now)
    if len(amb) < FOLLOW["ambient_min"]:
        return                                          # too little around to tell; keep the current place
    locs = sc["locs"]
    if sc["cur"] is None:
        locs.append(set(amb))
        sc["cur"] = 0
        return
    here = locs[sc["cur"]]
    if len(amb & here) / len(amb) >= FOLLOW["overlap"]:
        here |= amb
        if len(here) > 400:
            here.intersection_update(amb | set(list(here)[-300:]))
        sc["pending"], sc["pending_n"] = None, 0
        return
    best, best_o = -1, 0.0                              # somewhere else: a place seen before, or a new one
    for idx, sig in enumerate(locs):
        o = len(amb & sig) / len(amb)
        if idx != sc["cur"] and o >= FOLLOW["overlap"] and o > best_o:
            best, best_o = idx, o
    if sc["pending"] == best:
        sc["pending_n"] += 1
    else:
        sc["pending"], sc["pending_n"] = best, 1
    if sc["pending_n"] >= 2:                            # two snapshots in a row, so a blip doesn't count as a move
        if best < 0:
            locs.append(set(amb))
            best = len(locs) - 1
        else:
            locs[best] |= amb
        sc["cur"], sc["pending"], sc["pending_n"] = best, None, 0

def follow_tick(now: float, dt: float):
    scene_tick(now)
    loc = SCENE["cur"] if SCENE["cur"] is not None else -1
    for dev in list(DEVICES.values()):
        if not follow_eligible(dev):
            continue
        near = now - dev.last <= FOLLOW["present"] and dev.ema >= FOLLOW["near_rssi"]
        t = TAILS.get(dev.mac)
        if t is None:
            if not near:
                continue
            t = TAILS[dev.mac] = Tail(dev.mac, now, now)
        t.label = clean(dev.ident.label or dev.name or "Tracker", 40)
        if near and dt > 0:
            t.near_s += dt
            t.locs[loc] = t.locs.get(loc, 0.0) + dt
            t.last = now
        places = sum(1 for k, sec in t.locs.items() if k >= 0 and sec >= FOLLOW["min_loc_s"])
        if places >= 3 and t.near_s >= FOLLOW["alert_s"]:
            tier = "alert"
        elif places >= 2 and t.near_s >= FOLLOW["suspect_s"]:
            tier = "suspect"
        elif t.near_s >= FOLLOW["watch_s"]:
            tier = "watch"
        else:
            tier = ""
        if FOLLOW_RANK[tier] > FOLLOW_RANK[t.tier]:
            follow_escalate(t, tier, places)

def follow_escalate(t: Tail, tier: str, places: int):
    t.tier = tier
    log_event(f"Follower {tier.upper()}: {t.label} ({t.mac}), {places} place(s), {fmt_dur(t.near_s, True)} close",
              "follower" if tier != "watch" else "info")
    if tier != "watch":
        game_on_follower(t)
    if tier == "watch":
        STATUS.set(f"👁 Watching {t.label}: close to you for {fmt_dur(t.near_s, True)} (movement unknown)")
        return
    t.flagged = True
    word = "ALERT" if tier == "alert" else "SUSPECT"
    STATUS.set(f"⚠ FOLLOWER {word}: {t.label} ({t.mac}) near you across {places} places "
               f"({fmt_dur(t.near_s, True)} close). Press f.")
    play_notification_sound()

def follow_rows() -> list:
    return sorted(TAILS.values(), key=lambda t: (-FOLLOW_RANK[t.tier], -t.near_s))

def follow_alerts() -> int:
    return sum(1 for t in TAILS.values() if FOLLOW_RANK[t.tier] >= 2)

# =============================================================================
# TRACKING & RENDERING
# =============================================================================
@dataclass
class Dev:
    mac: str
    first: float
    last: float
    name: str = ""
    kind: str = "unknown"
    rssi: int = -100
    ema: float = -100.0
    ble: object = None          # latest bleak BLEDevice, so a connect can skip re-discovery
    sensor: object = None       # decoded sensor broadcast (see decode_sensor), with "t" = when it was last decoded
    classic: bool = False       # heard through classic Bluetooth (BR/EDR) discovery
    cod: int = 0                # classic Class-of-Device value
    tx: object = None
    packets: int = 0
    hist: collections.deque = field(default_factory=collections.deque)
    mfg_ids: set = field(default_factory=set)
    mfg_text: str = ""
    uuids: set = field(default_factory=set)
    fp: tuple = ()
    ident: Identity = field(default_factory=Identity)
    passed: bool = False        # currently clears the signal filter
    counted: bool = False       # already counted in the "seen" total
    ghost_id: str = ""          # cross-MAC identity cluster this device is linked to (see ghost_link)
    peak: int = -127            # strongest raw RSSI seen this session

DEVICES: dict[str, Dev] = {}
SEEN: set = set()
LAST_ALERT: dict = {}

# -----------------------------------------------------------------------------
# MAC-randomization-resistant fingerprinting ("ghosts")
#
# iOS/Android privacy features rotate private BLE addresses every ~15 minutes,
# which normally makes a device look like a brand-new stranger each time. Many
# devices keep broadcasting the *same shape* of advertisement across a rotation
# (same local name, same manufacturer-data type markers, same service UUIDs) --
# make_fp() already strips the bits that change per-packet (e.g. Apple's
# rotating encrypted payload is reduced to its stable type tuple). A "ghost" is
# a cluster of MACs believed to be the same physical radio across time, matched
# on that content fingerprint plus a plausibility check (did it show up within
# a normal rotation window, and did the signal strength jump too far to be the
# same device standing roughly still).
#
# This is inherently probabilistic, not a cryptographic identity: a generic,
# content-free advertisement (no name, no mfg data, no UUIDs) is excluded
# entirely since it would just glue unrelated devices together.
# -----------------------------------------------------------------------------
@dataclass
class Ghost:
    id: str
    fp: tuple
    macs: list = field(default_factory=list)     # chronological MACs believed to be this device
    first: float = 0.0
    last: float = 0.0
    last_rssi: float = -100.0
    rotations: int = 0

GHOSTS: dict[str, Ghost] = {}
FP_INDEX: dict[tuple, list] = {}       # fp -> [ghost_id, ...]; several physical devices can share a generic fp
GHOST_ROTATION_WINDOW = 20 * 60        # seconds; private addresses typically rotate every ~15 min
GHOST_RSSI_SLOP = 18                   # dB; max plausible jump between the old MAC's last reading and the new MAC's first
GHOST_STALE = 3600.0                   # seconds; drop ghosts nothing has matched against in an hour

FINDMY_RSSI_SLOP = 12                  # dB; tighter than other devices because every AirTag shares one fingerprint
FINDMY_LIVE_S = 10.0                   # seconds; a cluster address heard this recently is still in use, so a new address is a different tag

def is_findmy_fp(fp: tuple) -> bool:
    """Apple Find My beacon (AirTag / accessory): Apple manufacturer data carrying Continuity type 0x12."""
    try:
        return any(cid == 0x004C and 0x12 in types for cid, types in fp[1])
    except (TypeError, IndexError):
        return False

def fp_distinctive(fp: tuple) -> bool:
    """A fingerprint is only trustworthy for linking if it actually carries content."""
    name, mfg_parts, uuids = fp
    return bool(name) or bool(mfg_parts) or bool(uuids)

def ghost_link(dev: "Dev", now: float):
    """Correlate a rotating private address with past MACs sharing its advertisement
    fingerprint, so the same physical device can be tracked across address changes."""
    findmy = is_findmy_fp(dev.fp)
    if dev.kind not in ("private-resolvable", "private-nonresolvable") and not (findmy and dev.kind == "static-random"):
        return
    fp = dev.fp
    if not fp_distinctive(fp):
        return

    candidates = FP_INDEX.get(fp, [])
    for gid in candidates:
        ghost = GHOSTS[gid]
        if dev.mac in ghost.macs:
            dev.ghost_id = gid
            ghost.last, ghost.last_rssi = now, dev.ema
            return

    best = None
    for gid in candidates:
        ghost = GHOSTS[gid]
        gap = now - ghost.last
        slop = FINDMY_RSSI_SLOP if findmy else GHOST_RSSI_SLOP
        if findmy and any((o := DEVICES.get(m)) is not None and m != dev.mac and now - o.last < FINDMY_LIVE_S
                          for m in ghost.macs):
            continue          # an address in this cluster is still advertising: that is a different tag, not a rotation
        if gap <= GHOST_ROTATION_WINDOW and abs(dev.ema - ghost.last_rssi) <= slop:
            if best is None or ghost.last > GHOSTS[best].last:
                best = gid

    if best:
        ghost = GHOSTS[best]
        ghost.macs.append(dev.mac)
        ghost.rotations += 1
        ghost.last, ghost.last_rssi = now, dev.ema
        dev.ghost_id = best
        game_on_rotation()
        STATUS.set(f"Probable MAC rotation: {dev.mac} linked to ghost #{best} "
                    f"({ghost.rotations} rotation{'s' if ghost.rotations != 1 else ''} tracked)")
        play_notification_sound()
        return

    gid = hashlib.sha1(f"{fp!r}|{dev.mac}|{now}".encode()).hexdigest()[:8]
    GHOSTS[gid] = Ghost(id=gid, fp=fp, macs=[dev.mac], first=now, last=now, last_rssi=dev.ema)
    FP_INDEX.setdefault(fp, []).append(gid)
    dev.ghost_id = gid

def ghost_alias(dev: "Dev"):
    """If this MAC is a probable rotation of a device already named/known under a past
    MAC, resolve to that name instead of showing a fresh stranger."""
    if not dev.ghost_id or dev.ghost_id not in GHOSTS:
        return None
    for m in GHOSTS[dev.ghost_id].macs:
        if m == dev.mac:
            continue
        if KNOWN and m in KNOWN.renames:
            return KNOWN.renames[m]
        if m in CFG_NAMES:
            return CFG_NAMES[m]
    return None

def prune_ghosts(now: float):
    """Drop ghost clusters nothing has matched against in a while, so a long-running
    session doesn't accumulate stale identity clusters forever."""
    dead = [gid for gid, g in GHOSTS.items() if now - g.last > GHOST_STALE]
    for gid in dead:
        g = GHOSTS.pop(gid)
        if len(g.macs) > 1:
            ARCHIVED_GHOSTS.append(g)
        lst = FP_INDEX.get(g.fp)
        if lst and gid in lst:
            lst.remove(gid)
            if not lst:
                del FP_INDEX[g.fp]
STATS = {"packets": 0, "pps": 0.0}
CFG = {
    "log_file": "cops.log",
    "min_rssi": None,        # smoothed-RSSI display filter in dBm (None = off); keys [ ] l
    "rssi_hyst": 4,          # dB of hysteresis so devices do not flicker at the threshold
    "rssi_bypass": True,     # alerts, known devices and the hunted device ignore the filter (key a)
    "stale": 10.0,
    "subtitles": True,
    "civilian_filter": False,
    "scanning": True,
    "view_mode": 0,          # index into view_list(): grid, compact, tactical, security, then one view per category
    "show_help": False,      # Toggled via shortcut 'h'
    "show_follow": False,    # Toggled via shortcut 'f'
    "show_hunt": False,      # Toggled via shortcut 'g' (while a hunt is active)
    "show_inspect": False,   # Opened via shortcut 'c' / Enter (device inspector)
    "show_profile": False,   # Toggled via shortcut 'p' (player profile)
    "show_tutorial": False,  # Toggled via shortcut 'b' (guide / tutorial)
    "show_missions": False,  # Toggled via shortcut 'y' (mission board; while the inspector is open, y connects to the device instead)
    "classic": False,        # Toggled via shortcut 'k' (classic Bluetooth discovery)
    "boot": True,            # play the fake boot sequence at launch (--no-boot / --boot, or "boot" in lookout_settings.json)
    "boot_sound": True,      # the boot sequence plays the intro sound
    "dedup": True,           # Toggled via shortcut 'd' (collapse rotating MACs)
    "fx": True,              # Toggled via shortcut 'z' (celebration + live visual effects)
    "crt": True,             # Toggled via shortcut 'o' (CRT scanlines)
    "auto_tactical": True,   # Toggled via shortcut 'u' (jump to the tactical view when a tactical device is found)
}
TACTICAL_SOUND = "government"   # plays government.mp3 (next to the script) the first time each tactical device is flagged
AUTO = {"pending": None}     # (mac, tier, label) of a newly flagged device waiting for the main loop to switch views
MUTED = False                # Toggled via shortcut 'm'

# -----------------------------------------------------------------------------
# Supporter / donations (honor system)
# Press $ -> read about donating -> agree -> donate via the link -> type the unlock code to activate.
# Nothing is verified: it is an honor system. Supporters get a sparkling player name in the HUD and a
# gold sparkling SUPPORTER badge on their profile. The status is saved in lookout_settings.json.
# -----------------------------------------------------------------------------
DONATE_URL = "https://www.paypal.com/ncp/payment/9Z8GWNZFJLK7G"
SUPPORT_CODE = "NOMAD-SUPPORTER"        # change this to whatever code you want donors to type
SUPPORT = {"on": False}

def sparkle_text(txt: str, now: float, glyphs: bool = True, base: str = "gold1") -> "Text":
    """Gold text with a bright shimmer sweeping across it and twinkling stars on both sides.
    With visual effects off (z) it stays plain gold."""
    t = Text(no_wrap=True)
    fx = CFG["fx"]
    n = len(txt)
    pos = (now * 9.0) % (n + 10) - 5
    if glyphs:
        t.append(("✦" if int(now * 3) % 2 == 0 else "✧") + " " if fx else "★ ", style="bold bright_yellow")
    for i, c in enumerate(txt):
        d = abs(i - pos)
        if not fx:
            sty = f"bold {base}"
        elif d < 1.0:
            sty = "bold bright_white"
        elif d < 2.5:
            sty = "bold bright_yellow"
        else:
            sty = f"bold {base}"
        t.append(c, style=sty)
    if glyphs:
        t.append((" " + ("✧" if int(now * 3) % 2 == 0 else "✦")) if fx else " ★", style="bold bright_yellow")
    return t
NOTIFY_SOUNDS = [("notify", "notify.mp3"), ("notify2", "notify2.mp3"), ("notify3", "notify3.mp3"), (None, "OFF")]
NOTIFY = {"idx": 0}          # Cycled via shortcut 'n': sound played when a new device is found (None = silent)
RSSI_FLOOR = -127            # raw packets weaker than this are discarded outright
RSSI_PRESETS = [None, -90, -80, -70, -60, -50]     # [ and ] walk this list (None = off)

# -----------------------------------------------------------------------------
# Signal-strength filtering
# -----------------------------------------------------------------------------
def passes_signal(dev, now=None) -> bool:
    """Display / credit filter on the SMOOTHED RSSI with hysteresis. Raw packets are always tracked so
    follower detection and hunt mode keep their data; alerts, known devices and the hunted device can bypass."""
    thr = CFG["min_rssi"]
    if thr is None:
        dev.passed = True
        return True
    if CFG["rssi_bypass"] and (dev.ident.tier in ("alert", "possible", "known") or dev.mac == HUNT["mac"]):
        dev.passed = True
        return True
    dev.passed = dev.ema >= (thr - CFG["rssi_hyst"] if dev.passed else thr)
    return dev.passed

def hidden_count(now) -> int:
    if CFG["min_rssi"] is None:
        return 0
    return sum(1 for d in DEVICES.values() if now - d.last <= CFG["stale"] and not passes_signal(d, now))

def save_settings():
    try:
        tmp = SETTINGS_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump({"min_rssi": CFG["min_rssi"], "rssi_bypass": CFG["rssi_bypass"], "fx": CFG["fx"],
                       "crt": CFG["crt"], "notify_idx": NOTIFY["idx"], "supporter": SUPPORT["on"],
                       "auto_tactical": CFG["auto_tactical"], "tutorial_seen": TUT["seen"],
                       "classic": CFG["classic"], "boot": CFG["boot"], "boot_sound": CFG["boot_sound"]}, f, indent=2)
        os.replace(tmp, SETTINGS_FILE)
    except Exception:
        pass

def load_settings():
    try:
        with open(SETTINGS_FILE) as f:
            d = json.load(f)
        v = d.get("min_rssi")
        CFG["min_rssi"] = int(v) if isinstance(v, (int, float)) and RSSI_FLOOR <= v < 0 else None
        CFG["rssi_bypass"] = bool(d.get("rssi_bypass", True))
        CFG["fx"] = bool(d.get("fx", True))
        CFG["crt"] = bool(d.get("crt", True))
        SUPPORT["on"] = bool(d.get("supporter", False))
        CFG["auto_tactical"] = bool(d.get("auto_tactical", True))
        CFG["classic"] = bool(d.get("classic", False))
        CFG["boot"] = bool(d.get("boot", True))
        CFG["boot_sound"] = bool(d.get("boot_sound", True))
        TUT["seen"] = bool(d.get("tutorial_seen", False))
        ni = d.get("notify_idx", 0)
        NOTIFY["idx"] = ni if isinstance(ni, int) and 0 <= ni < len(NOTIFY_SOUNDS) else 0
    except Exception:
        pass

def set_min_rssi(value, quiet=False):
    CFG["min_rssi"] = value
    save_settings()
    if not quiet:
        STATUS.set("Signal filter: OFF (showing every device)" if value is None else f"Signal filter: showing devices stronger than {value} dBm")

def step_min_rssi(direction: int):
    """direction +1 = tighter (stronger signals only), -1 = looser."""
    vals = [RSSI_FLOOR if v is None else v for v in RSSI_PRESETS]
    cur = RSSI_FLOOR if CFG["min_rssi"] is None else CFG["min_rssi"]
    if direction > 0:
        nxt = next((v for v in vals if v > cur), vals[-1])
    else:
        nxt = next((v for v in reversed(vals) if v < cur), vals[0])
    set_min_rssi(None if nxt <= RSSI_FLOOR else nxt)

def apply_signal_input(raw: str) -> str:
    if raw in ("", "0", "off", "OFF"):
        set_min_rssi(None, quiet=True)
        return "Signal filter: OFF"
    try:
        v = int(raw)
    except ValueError:
        return f"'{raw}' is not a number. Filter unchanged."
    if not (-110 <= v <= -20):
        return "Use a value between -110 and -20 dBm (e.g. -75). Filter unchanged."
    set_min_rssi(v, quiet=True)
    return f"Signal filter: showing devices stronger than {v} dBm"

def count_device(dev):
    """Count a device in the 'seen' total the first time it clears the signal filter."""
    if dev.mac not in SEEN:
        SEEN.add(dev.mac)
        game_on_new_device(dev)
        snd = NOTIFY_SOUNDS[NOTIFY["idx"]][0]
        is_tactical = getattr(getattr(dev, "ident", None), "tier", None) in ("alert", "possible")
        if snd and not is_tactical:                                # None = "no notify sound"; tactical devices get government.mp3 instead
            play_notification_sound(snd)

def count_tick(now):
    """Count devices that start passing the filter because it was loosened or their signal improved."""
    for d in list(DEVICES.values()):
        if not d.counted and now - d.last <= CFG["stale"] and passes_signal(d, now):
            d.counted = True
            count_device(d)

def get_props(device) -> dict:
    d = getattr(device, "details", None)
    if isinstance(d, dict) and isinstance(d.get("props"), dict):
        return d["props"]
    return {}

def make_fp(name, mfg, uuids):
    parts = []
    for cid, data in mfg.items():
        parts.append((cid, tuple(apple_types(data)) if cid == 0x004C else bytes(data[:2])))
    return (name, tuple(sorted(parts, key=lambda p: p[0])), tuple(sorted(uuids)))

def adv_clues(d) -> str:
    """Raw advertisement clues (company IDs, service UUIDs): what a rule in scanner_config.json can match on."""
    bits = []
    if d.mfg_ids:
        bits.append("mfg " + ",".join(f"0x{c:04X}" for c in sorted(d.mfg_ids)))
    if d.uuids:
        bits.append("svc " + ",".join(sorted(d.uuids)[:6]))
    return " · ".join(bits)

def mfg_label(mfg) -> str:
    return " | ".join(REG.company_name(cid) or f"0x{cid:04X}" for cid in mfg)

# -----------------------------------------------------------------------------
# Name-based ignore: hide every device whose advertised name OR identified label (what the dashboard
# shows, e.g. "Apple Find My beacon (AirTag / accessory)") matches a pattern.
#   plain text      exact name, case-insensitive          My Speaker
#   wildcards       * ? [seq], case-insensitive           Galaxy Buds*   /   *TV*
#   re:<regex>      regular expression, searched anywhere re:^(Tile|SmartTag)
# Sources: config "ignore_names", the saved list in lookout_known.json (key i), and --ignore-name (this run only).
# A name often arrives in a later packet than the first one (scan response), so a device can be created
# unnamed and then removed as soon as its name is heard; its MAC is then remembered and skipped from there on.
# -----------------------------------------------------------------------------
NAME_IGNORED_MACS: set = set()      # MACs already matched by a name pattern this run
SESSION_IGNORE_NAMES: list = []     # --ignore-name patterns (this run only)
_NAME_RX_CACHE: dict = {}

def all_ignore_name_patterns() -> list:
    pats = list(CFG_IGNORE_NAMES) + list(SESSION_IGNORE_NAMES)
    if KNOWN:
        pats += KNOWN.ignored_names
    return pats

def name_pattern_matches(pat: str, name: str) -> bool:
    if pat[:3].lower() == "re:":
        rx = _NAME_RX_CACHE.get(pat)
        if rx is None:
            try:
                rx = re.compile(pat[3:], re.I)
            except re.error:
                rx = False
            _NAME_RX_CACHE[pat] = rx
        return bool(rx) and bool(rx.search(name))
    return fnmatch.fnmatchcase(name.lower(), pat.lower())

def name_is_ignored(name: str) -> bool:
    return bool(name) and any(name_pattern_matches(p, name) for p in all_ignore_name_patterns())

def purge_device(mac: str):
    """Remove a device and any trace of it from the ghost index."""
    dev = DEVICES.pop(mac, None)
    SEEN.discard(mac)
    if dev is None:
        return
    g = GHOSTS.get(dev.ghost_id)
    if g:
        if mac in g.macs:
            g.macs.remove(mac)
        if not g.macs:
            GHOSTS.pop(g.id, None)
            lst = FP_INDEX.get(g.fp)
            if lst and g.id in lst:
                lst.remove(g.id)
                if not lst:
                    FP_INDEX.pop(g.fp, None)

def purge_name_matches() -> int:
    """Apply the current name patterns to devices already on screen; returns how many were hidden."""
    hit = [m for m, d in DEVICES.items() if name_is_ignored(d.name) or name_is_ignored(d.ident.label)]
    for m in hit:
        NAME_IGNORED_MACS.add(m)
        purge_device(m)
    return len(hit)

REALERT_GAP = 300.0           # seconds: a flagged device unheard this long alerts (and switches view) again when it returns

def announce_flag(dev, mac: str, rssi, first: bool = True):
    """Alert for an ALERT / POSSIBLE (tactical) device: log, sound, and queue the auto-switch to the Tactical view."""
    tier = dev.ident.tier
    label = dev.ident.label or dev.name or mac
    if first:
        EVENT_FLAGGED.add(mac)
        log_event(f"{tier.upper()} detected: {label} ({mac}) at {rssi} dBm", tier)
        game_on_flag(dev)                                     # XP / coins / quests (deduplicated per device)
    else:
        log_event(f"{tier.upper()} back in range: {label} ({mac}) at {rssi} dBm", tier)
    play_notification_sound(TACTICAL_SOUND)                   # government.mp3 (falls back to notify, then the bell)
    if CFG["auto_tactical"]:
        AUTO["pending"] = (mac, tier, label)

def on_detect(device, adv):
    mac = device.address.upper()
    if (KNOWN and mac in KNOWN.ignored) or mac in CFG_IGNORE or mac in NAME_IGNORED_MACS:
        return
    rssi = adv.rssi
    if rssi is None or rssi < RSSI_FLOOR:
        return
    adv_name = clean(adv.local_name or getattr(device, "name", "") or "")
    if adv_name and name_is_ignored(adv_name):
        if len(NAME_IGNORED_MACS) > 5000:             # rotating MACs: bounded; a cleared MAC is simply re-matched by name
            NAME_IGNORED_MACS.clear()
        NAME_IGNORED_MACS.add(mac)
        purge_device(mac)
        return
    now = time.time()
    STATS["packets"] += 1
    dev = DEVICES.get(mac)
    props = get_props(device)
    if dev is None:
        dev = DEVICES[mac] = Dev(mac=mac, first=now, last=now, kind=addr_kind(mac, props), ema=float(rssi))

    prev_seen = dev.last                                  # when we last heard this device (for re-alert on return)
    dev.last, dev.rssi, dev.tx = now, rssi, adv.tx_power
    dev.peak = max(dev.peak, rssi)
    dev.ema = 0.3 * rssi + 0.7 * dev.ema
    dev.packets += 1
    dev.hist.append((now, rssi))
    while dev.hist and now - dev.hist[0][0] > 45:
        dev.hist.popleft()

    dev.ble = device
    name = clean(adv.local_name or getattr(device, "name", "") or "")
    mfg = adv.manufacturer_data or {}
    if mfg or adv.service_data:
        sens = decode_sensor(name, mfg, adv.service_data or {})
        if sens:
            sens["t"] = now
            dev.sensor = sens
    uuids = {short_uuid(u) for u in (adv.service_uuids or [])} | {short_uuid(u) for u in (adv.service_data or {})}
    fp = make_fp(name, mfg, uuids)
    announced = False
    if fp != dev.fp:
        dev.fp, dev.name, dev.mfg_ids, dev.uuids = fp, name, set(mfg), uuids
        dev.mfg_text = mfg_label(mfg)
        user_label = CFG_NAMES.get(mac) or (KNOWN.renames.get(mac) if KNOWN else "") or ""
        dev.ident = identify(mac, name or user_label, mfg, uuids, props, dev.kind, KNOWN)   # a device you named is classified by that name when it advertises none
        if name_is_ignored(dev.ident.label):              # the scanner's own label, e.g. "Apple Find My beacon (...)"
            if len(NAME_IGNORED_MACS) > 5000:
                NAME_IGNORED_MACS.clear()
            NAME_IGNORED_MACS.add(mac)
            purge_device(mac)
            return
        ghost_link(dev, now)
        if dev.ident.tier in ("alert", "possible") and mac not in EVENT_FLAGGED:
            announce_flag(dev, mac, rssi, first=True)
            announced = True
    elif dev.ghost_id in GHOSTS:
        # Keep the ghost's "last seen" fresh on every packet, not just fp changes,
        # so a device that sits quietly for a while before rotating isn't
        # mistaken for one that went stale and rotated hours ago.
        ghost = GHOSTS[dev.ghost_id]
        ghost.last, ghost.last_rssi = now, dev.ema
    if (not announced and dev.ident.tier in ("alert", "possible") and mac in EVENT_FLAGGED
            and now - prev_seen > REALERT_GAP):
        announce_flag(dev, mac, rssi, first=False)            # a flagged device left and came back: alert again
    if not dev.counted and passes_signal(dev, now):
        dev.counted = True
        count_device(dev)

def trend(dev: Dev, now: float):
    recent = [r for t, r in dev.hist if now - t <= 8]
    older = [r for t, r in dev.hist if 8 < now - t <= 35]
    if not recent or not older:
        return "→", "dim"
    d = sum(recent) / len(recent) - sum(older) / len(older)
    return ("↑", "green") if d > 1.5 else ("↓", "red") if d < -1.5 else ("→", "dim")

def sig_bar(r: float):
    lvl = 4 if r >= -55 else 3 if r >= -67 else 2 if r >= -80 else 1 if r >= -90 else 0
    col = "green" if lvl >= 3 else "yellow" if lvl == 2 else "red"
    t = Text()
    for i, g in enumerate("▂▄▆█"):
        t.append(g, style=col if i < lvl else "grey30")
    return t

def meter(dev: Dev, now: float, style: str):
    sym, col = trend(dev, now)
    d_ft = est_distance_ft(dev.ema, dev.tx)
    d_str = ">300ft" if d_ft > 300 else f"{d_ft:.1f}ft"
    t = Text(f"{dev.ema:>4.0f} ", style=style)
    t.append_text(sig_bar(dev.ema))
    t.append(f" {d_str:>6} ", style=style)
    t.append(sym, style=col)
    return t

# =============================================================================
# SENSOR DECODER
# Many cheap sensors broadcast their readings in the open, so no connection is needed. Formats decoded:
#   BTHome v2 (service data 0xFCD2, unencrypted)     temperature, humidity, pressure, light, CO2, battery, door/motion ...
#   ATC1441 / PVVX custom Xiaomi thermometers (0x181A) temperature, humidity, battery
#   Ruuvi RAWv2 (manufacturer 0x0499, format 5)        temperature, humidity, pressure, motion, battery
#   Govee H5074 / H5075 / H5072 (manufacturer 0xEC88)  temperature, humidity, battery
# Encrypted broadcasts (BTHome with encryption, Xiaomi MiBeacon) cannot be read and are simply left alone.
# =============================================================================
SENSOR_TEMP_UNIT = "F"          # "F" or "C": how temperatures are shown
SENSOR_STALE = 300.0            # seconds a sensor stays listed in the Sensors view after it was last heard

def _svc(sd: dict, short: int):
    return sd.get(f"0000{short:04x}-0000-1000-8000-00805f9b34fb")

def fmt_temp(c: float) -> str:
    return f"{c * 9 / 5 + 32:.1f}°F" if SENSOR_TEMP_UNIT == "F" else f"{c:.1f}°C"

def _i(b: bytes, o: int, n: int, signed=False, big=False) -> int:
    return int.from_bytes(b[o:o + n], "big" if big else "little", signed=signed)

# id: (label, bytes, signed, factor, unit)
BTHOME_NUM = {
    0x01: ("Battery", 1, False, 1, "%"), 0x02: ("Temp", 2, True, 0.01, "C"), 0x03: ("Humidity", 2, False, 0.01, "%"),
    0x04: ("Pressure", 3, False, 0.01, " hPa"), 0x05: ("Light", 3, False, 0.01, " lx"), 0x08: ("Dew point", 2, True, 0.01, "C"),
    0x0B: ("Power", 3, False, 0.01, " W"), 0x0C: ("Voltage", 2, False, 0.001, " V"), 0x0D: ("PM2.5", 2, False, 1, " µg/m³"),
    0x0E: ("PM10", 2, False, 1, " µg/m³"), 0x12: ("CO₂", 2, False, 1, " ppm"), 0x13: ("TVOC", 2, False, 1, " µg/m³"),
    0x14: ("Moisture", 2, False, 0.01, "%"), 0x2E: ("Humidity", 1, False, 1, "%"), 0x2F: ("Moisture", 1, False, 1, "%"),
    0x43: ("Current", 2, False, 0.001, " A"), 0x45: ("Temp", 2, True, 0.1, "C"), 0x46: ("UV index", 1, False, 0.1, ""),
}
BTHOME_BOOL = {
    0x0F: ("Generic", "off", "on"), 0x10: ("Power", "off", "on"), 0x11: ("Opening", "closed", "OPEN"),
    0x15: ("Battery", "ok", "LOW"), 0x16: ("Charging", "no", "yes"), 0x17: ("CO", "clear", "DETECTED"),
    0x1A: ("Door", "closed", "OPEN"), 0x1C: ("Gas", "clear", "DETECTED"), 0x1F: ("Lock", "locked", "UNLOCKED"),
    0x20: ("Moisture", "dry", "WET"), 0x21: ("Motion", "clear", "MOTION"), 0x22: ("Moving", "no", "yes"),
    0x23: ("Occupancy", "clear", "OCCUPIED"), 0x25: ("Presence", "away", "home"), 0x29: ("Smoke", "clear", "SMOKE"),
    0x2B: ("Tamper", "clear", "TAMPER"), 0x2D: ("Window", "closed", "OPEN"),
}

def _num_text(label: str, val: float, unit: str) -> str:
    if unit == "C":
        return fmt_temp(val)
    return f"{val:.2f}".rstrip("0").rstrip(".") + unit

def decode_bthome(data: bytes):
    if len(data) < 2:
        return None
    info = data[0]
    if (info >> 5) & 7 != 2:
        return None                                   # not BTHome v2
    if info & 1:
        return {"fmt": "BTHome v2 (encrypted)", "vals": []}
    vals, i = [], 1
    while i < len(data):
        oid = data[i]
        i += 1
        if oid == 0x00:                               # packet id
            i += 1
            continue
        if oid in BTHOME_NUM:
            label, n, signed, factor, unit = BTHOME_NUM[oid]
            if i + n > len(data):
                break
            vals.append((label, _num_text(label, _i(data, i, n, signed) * factor, unit)))
            i += n
        elif oid in BTHOME_BOOL and i < len(data):
            label, off, on = BTHOME_BOOL[oid]
            vals.append((label, on if data[i] else off))
            i += 1
        else:
            break                                     # unknown object: its length is unknown, so stop here
    return {"fmt": "BTHome v2", "vals": vals} if vals else None

def decode_atc(data: bytes):
    if len(data) == 13:                               # ATC1441: mac(6) temp(2 BE, 0.1) hum(1) batt%(1) mV(2 BE) counter(1)
        return {"fmt": "ATC1441 thermometer", "vals": [
            ("Temp", fmt_temp(_i(data, 6, 2, True, True) / 10)), ("Humidity", f"{data[8]}%"),
            ("Battery", f"{data[9]}% ({_i(data, 10, 2, False, True) / 1000:.2f} V)")]}
    if len(data) == 15:                               # PVVX: mac(6) temp(2 LE, 0.01) hum(2 LE, 0.01) mV(2 LE) batt%(1) counter(1) flags(1)
        return {"fmt": "PVVX thermometer", "vals": [
            ("Temp", fmt_temp(_i(data, 6, 2, True) / 100)), ("Humidity", f"{_i(data, 8, 2) / 100:.1f}%"),
            ("Battery", f"{data[12]}% ({_i(data, 10, 2) / 1000:.2f} V)")]}
    return None

def decode_ruuvi(data: bytes):
    if len(data) < 24 or data[0] != 5:
        return None
    vals = []
    t = _i(data, 1, 2, True, True)
    if t != -32768:
        vals.append(("Temp", fmt_temp(t * 0.005)))
    h = _i(data, 3, 2, False, True)
    if h != 0xFFFF:
        vals.append(("Humidity", f"{h * 0.0025:.1f}%"))
    p = _i(data, 5, 2, False, True)
    if p != 0xFFFF:
        vals.append(("Pressure", f"{(p + 50000) / 100:.1f} hPa"))
    acc = [_i(data, o, 2, True, True) for o in (7, 9, 11)]
    if all(a != -32768 for a in acc):
        vals.append(("Accel (mg)", f"x {acc[0]} · y {acc[1]} · z {acc[2]}"))
    pw = _i(data, 13, 2, False, True)
    if pw >> 5 != 2047:
        vals.append(("Battery", f"{((pw >> 5) + 1600) / 1000:.3f} V"))
    if data[15] != 0xFF:
        vals.append(("Movements", str(data[15])))
    return {"fmt": "Ruuvi RAWv2", "vals": vals}

def decode_govee(name: str, data: bytes):
    n = name.lower()
    if "5074" in n and len(data) >= 6:
        return {"fmt": "Govee H5074", "vals": [
            ("Temp", fmt_temp(_i(data, 1, 2, True) / 100)), ("Humidity", f"{_i(data, 3, 2) / 100:.1f}%"),
            ("Battery", f"{data[5]}%")]}
    if ("5075" in n or "5072" in n) and len(data) >= 5:
        v = _i(data, 1, 3, False, True)
        neg = bool(v & 0x800000)
        v &= 0x7FFFFF
        temp = int(v / 1000) / 10 * (-1 if neg else 1)
        return {"fmt": "Govee H5075/H5072", "vals": [
            ("Temp", fmt_temp(temp)), ("Humidity", f"{(v % 1000) / 10:.1f}%"), ("Battery", f"{data[4]}%")]}
    return None

def decode_sensor(name: str, mfg: dict, sd: dict):
    """Return {'fmt', 'vals': [(label, text)], 'summary'} for a recognised sensor broadcast, else None."""
    res = None
    try:
        if sd:
            b = _svc(sd, 0xFCD2)
            if b is not None:
                res = decode_bthome(bytes(b))
            if res is None:
                b = _svc(sd, 0x181A)
                if b is not None:
                    res = decode_atc(bytes(b))
        if res is None and mfg:
            if 0x0499 in mfg:
                res = decode_ruuvi(bytes(mfg[0x0499]))
            elif 0xEC88 in mfg:
                res = decode_govee(name or "", bytes(mfg[0xEC88]))
    except Exception:
        return None
    if res is None:
        return None
    vals = res["vals"]
    main = [v for k, v in vals if k not in ("Battery", "Accel (mg)", "Movements", "Dew point")][:2]
    batt = next((v for k, v in vals if k == "Battery"), "")
    res["summary"] = " ".join(main) + (f" 🔋{batt.split(' ')[0]}" if batt else "")
    if res["fmt"].endswith("(encrypted)"):
        res["summary"] = "🔒 encrypted"
    return res

def sensor_summary(dev) -> str:
    s = getattr(dev, "sensor", None)
    return (s or {}).get("summary", "")

def friendly_name(dev: Dev) -> str:
    """Advertised name, with machine-generated ones replaced by something readable.
    Tesla phone-key beacons advertise S<16 hex>C; show 'Tesla Car (…1234)' (last 4 hex keeps two cars apart)."""
    n = dev.name or ""
    if n and TESLA_NAME.match(n.lower()):
        return f"Tesla Car (…{n[-5:-1]})"
    return n

def display_name(dev: Dev, sensor: bool = True) -> str:
    alias = None
    if KNOWN and dev.mac in KNOWN.renames:
        base = KNOWN.renames[dev.mac]
    elif dev.mac in CFG_NAMES:
        base = CFG_NAMES[dev.mac]
    else:
        alias = ghost_alias(dev)
        base = f"{alias} (new MAC)" if alias else (friendly_name(dev) or dev.ident.label or f"{dev.mac[-8:]}")
    icon = CATEGORY_ICONS.get(dev.ident.category, "🔌")
    rotations = len(GHOSTS[dev.ghost_id].macs) if dev.ghost_id in GHOSTS else 0
    tag = f" 👻×{rotations}" if rotations > 1 else ""
    reading = sensor_summary(dev) if sensor else ""
    return f"{icon} {base}{tag}" + (f" · {reading}" if reading else "")

def sub_text(dev: Dev) -> str:
    i = dev.ident
    bits = []
    if i.label and i.label != dev.name:
        bits.append(i.label)
    if i.vendor:
        bits.append(i.vendor)
    bits.append(i.addr_type)
    if dev.sensor and dev.sensor.get("summary"):
        bits.append(dev.sensor["summary"])
    if dev.ghost_id in GHOSTS and len(GHOSTS[dev.ghost_id].macs) > 1:
        bits.append(f"{len(GHOSTS[dev.ghost_id].macs)} MACs linked")
    return " · ".join(bits)

# =============================================================================
# LIVE VISUAL EFFECTS
# New-device flash, alert pulse, radar sweep, hunt sonar, HUD heartbeat, animated XP bar and CRT scanlines.
# Everything is a pure function of the clock (`now`), so the only state is the few small dicts below.
# Key z (or --no-fx) turns the motion off (the screens stay fully usable); key o toggles the CRT scanlines.
# =============================================================================
FLASH_SECONDS = 2.6          # how long a brand-new device stays highlighted
ANIM_TICK = 0.12             # seconds per frame while something is animating (the loop idles at 0.25 otherwise)
TWO_PI = 2 * math.pi

def _mix(c1, c2, t: float) -> str:
    """Colour between two (r, g, b) triples as a Rich 'rgb(r,g,b)' colour (Rich downgrades it on 256/16-colour terminals)."""
    t = max(0.0, min(1.0, t))
    return "rgb({},{},{})".format(*(int(a + (b - a) * t) for a, b in zip(c1, c2)))

def pulse(now: float, hz: float = 1.4) -> float:
    """Smooth 0..1 throb."""
    return 0.5 + 0.5 * math.sin(now * hz * TWO_PI)

# ---- new-device flash ------------------------------------------------------
def flash_style(dev, now: float, base: str):
    """(style, fresh). A device that just appeared blinks for ~1.2 s, glows cyan, then settles back to `base`."""
    if not CFG["fx"]:
        return base, False
    age = now - dev.first
    if age < 0 or age >= FLASH_SECONDS:
        return base, False
    if age < 1.2:
        return ("bold black on bright_white" if int(age / 0.2) % 2 == 0 else "bold bright_white"), True
    if age < 1.9:
        return "bold bright_cyan", True
    return base, True

def status_text(dev, now: float, live: bool) -> Text:
    """'● LIVE' / '○ RECENT' status cell, or a blinking '✦ NEW' for the first couple of seconds."""
    _, fresh = flash_style(dev, now, "")
    if fresh and now - dev.first < 1.9:
        return Text("✦ NEW", style="bold black on bright_white" if int((now - dev.first) / 0.2) % 2 == 0 else "bold bright_white")
    return Text("● LIVE" if live else "○ RECENT", style="bright_green" if live else "dim")

# ---- alert pulse -----------------------------------------------------------
def worst_tier(devs) -> str:
    tiers = {d.ident.tier for d in devs}
    return "alert" if "alert" in tiers else "possible" if "possible" in tiers else ""

def throb_border(base: str, level: str, now: float) -> str:
    """Border style for a panel holding flagged devices: red throb for 'alert', amber for 'possible'; `base` otherwise."""
    if not CFG["fx"] or level not in ("alert", "possible"):
        return base
    if level == "alert":
        return "bold " + _mix((110, 0, 0), (255, 70, 70), pulse(now, 1.5))
    return "bold " + _mix((120, 90, 0), (255, 205, 40), pulse(now, 0.9))

def throb_text(base: str, tier: str, now: float) -> str:
    """Text style that throbs for alert/possible tier devices (so flagged rows stand out inside any table)."""
    if not CFG["fx"] or tier not in ("alert", "possible"):
        return base
    if tier == "alert":
        return "bold " + _mix((190, 30, 30), (255, 140, 140), pulse(now, 1.5))
    return "bold " + _mix((170, 130, 0), (255, 225, 90), pulse(now, 0.9))

# ---- HUD heartbeat ---------------------------------------------------------
HEART = {"beats": collections.deque(maxlen=14), "next": 0.0, "rate": 0.0, "t": 0.0, "pk": 0, "last_pkt": 0.0}
HEART_COLS = 14
HEART_SLICE = 0.11
_ECG = "▂▃▂▁█▁▃▄▂"           # one beat: baseline, P wave, Q dip, R spike, S dip, T wave

def heart_tick(now: float):
    """Track the packet rate and schedule beats: the faster packets arrive, the faster the heart beats."""
    h, pk = HEART, STATS["packets"]
    if h["t"] == 0.0:
        h.update(t=now, pk=pk, next=now, last_pkt=now if pk else 0.0)
        return
    if pk != h["pk"]:
        h["last_pkt"] = now
    dt = now - h["t"]
    if dt >= 0.5:
        inst = (pk - h["pk"]) / dt
        h["rate"] = inst if h["rate"] == 0.0 else 0.6 * h["rate"] + 0.4 * inst
        STATS["pps"] = h["rate"]                      # the Statistics view / grid footer read this
        h["t"], h["pk"] = now, pk
    if CFG["scanning"] and now - h["last_pkt"] < 3.0 and now >= h["next"]:
        h["beats"].append(now)
        h["next"] = now + max(0.35, 1.8 - 0.55 * math.log10(1 + h["rate"]))
    elif not CFG["scanning"]:
        h["next"] = now

def heartbeat_text(now: float) -> Text:
    h = HEART
    t = Text(no_wrap=True)
    if not CFG["scanning"]:
        t.append("♡ ", style="dim")
        t.append("▁" * HEART_COLS, style="dim")
        t.append(" paused", style="dim")
        return t
    if not h["last_pkt"] or now - h["last_pkt"] >= 3.0:
        t.append("♥ ", style="bold red")
        t.append("▁" * HEART_COLS, style="red")
        t.append(" no packets", style="bold red")
        return t
    beats = list(h["beats"])
    since = now - beats[-1] if beats else 9.0
    t.append("♥ ", style="bold bright_red" if (since < 0.18 and CFG["fx"]) else "red")
    for i in range(HEART_COLS - 1, -1, -1):
        if not CFG["fx"]:
            t.append("▂", style="green")
            continue
        col_t = now - i * HEART_SLICE
        ch = "▂"
        for b in reversed(beats):
            if b <= col_t:
                idx = int((col_t - b) / HEART_SLICE)
                if idx < len(_ECG):
                    ch = _ECG[idx]
                break
        style = "bold bright_green" if ch == "█" else ("green" if i < HEART_COLS * 0.6 else "dim green")
        t.append(ch, style=style)
    t.append(f" {h['rate']:>4.0f} pkt/s", style="green")
    return t

# ---- animated XP bar -------------------------------------------------------
XPANIM = {"disp": None, "src": 0.0, "to": 0.0, "start": -99.0, "dur": 1.3, "gain": 0.0, "gain_t": -99.0}
_EIGHTHS = " ▏▎▍▌▋▊▉"

def xp_anim_tick(now: float):
    """Ease the displayed XP toward the real value; remember how much was just gained for the '+N' tag."""
    if not GAME["on"] or not STATE:
        return
    a, cur = XPANIM, float(STATE.get("xp", 0))
    if a["disp"] is None or not CFG["fx"]:
        a.update(disp=cur, src=cur, to=cur)
        return
    if cur > a["to"]:
        a["gain"] = (a["gain"] if now - a["gain_t"] < 2.5 else 0.0) + (cur - a["to"])
        a.update(src=a["disp"], to=cur, start=now, gain_t=now)
    elif cur < a["to"]:                               # XP was reset or edited: jump, don't animate
        a.update(disp=cur, src=cur, to=cur)
    t = (now - a["start"]) / a["dur"]
    if t >= 1.0:
        a["disp"] = a["to"]
    else:
        a["disp"] = a["src"] + (a["to"] - a["src"]) * (1 - (1 - max(0.0, t)) ** 3)      # ease-out

def game_progress_at(xp: float):
    """Like game_progress() but for an arbitrary (possibly in-between) XP value."""
    lvl, xs = game_level(int(xp)), GAME["level_xp"]
    if lvl >= len(xs):
        return lvl, 0, 0
    return lvl, xp - xs[lvl - 1], xs[lvl] - xs[lvl - 1]

def xp_bar(frac: float, width: int, now: float, base: str = "yellow") -> Text:
    """XP bar with smooth 1/8-cell fill, a glowing leading edge while it fills, and a shimmer sweep after a gain."""
    a = XPANIM
    cells = max(0.0, min(1.0, frac)) * width
    full, part = int(cells), int((cells - int(cells)) * 8)
    filled = full + (1 if part else 0)
    shim, filling = -9.0, False
    if CFG["fx"] and a["disp"] is not None:
        sp = (now - a["start"]) / (a["dur"] + 0.5)
        if 0.0 <= sp < 1.0:
            shim = sp * (filled + 4) - 2              # band centre runs from just before the bar to just past the fill
        filling = abs(a["disp"] - a["to"]) > 0.01
    t = Text(no_wrap=True)
    for i in range(width):
        if i < full:
            ch, sty = "█", base
        elif i == full and part:
            ch, sty = _EIGHTHS[part], base
        else:
            t.append("░", style="grey30")
            continue
        d = abs(i - shim)
        if d < 0.8:
            sty = "bold bright_white"
        elif d < 1.8:
            sty = "bold bright_yellow"
        elif filling and i == filled - 1:
            sty = "bold bright_yellow"
        t.append(ch, style=sty)
    return t

# ---- CRT scanlines ---------------------------------------------------------
class CRTScanlines:
    """Wraps the finished screen: every second text row is dimmed (scanlines) and a soft bright band rolls
    slowly down the screen like a CRT refresh. Pure post-processing; nothing underneath knows about it."""
    BAND = 3
    PERIOD = 9.0

    def __init__(self, inner, now: float):
        self.inner, self.now = inner, now

    def __rich_console__(self, console, options):
        lines = console.render_lines(self.inner, options, pad=True)
        n = len(lines)
        band = -99.0
        if CFG["fx"] and n:
            band = (self.now % self.PERIOD) / self.PERIOD * (n + self.BAND) - self.BAND
        dim, cache = Style(dim=True), {}
        for y, line in enumerate(lines):
            if y % 2 == 1 and not (band <= y < band + self.BAND):
                for seg in line:
                    if seg.control:
                        yield seg
                        continue
                    st = cache.get(seg.style)
                    if st is None:
                        st = cache[seg.style] = (seg.style + dim) if seg.style else dim
                    yield Segment(seg.text, st, seg.control)
            else:
                yield from line
            if y < n - 1:
                yield Segment.line()

def crt_wrap(renderable, now: float):
    """Whole-screen post-processing, innermost first: Intel Coins cosmetics (theme / neon / glitch), then the CRT scanlines."""
    if cosmetics_now(now):
        renderable = CosmeticFilter(renderable, now)
    return CRTScanlines(renderable, now) if CFG["crt"] else renderable

# ---- Intel Coins cosmetics: hacker themes, neon mode, glitch effects -------------------------------------------
# Everything here is pure post-processing of the finished screen (like the CRT filter): nothing underneath knows about it,
# and a bug in here can never take the dashboard down (CosmeticFilter falls back to the untouched screen).
# What is active comes from the shop items the player bought and equipped (see the INTEL COINS section further down).
# ALERT-red text and borders are never recoloured, so a tactical alert still looks like an alert in every theme.
COSMETIC_SLOTS = ("theme", "neon", "glitch", "decrypt")
PREVIEW = {"item": "", "until": 0.0}      # a shop item being tried on for a few seconds before buying
PREVIEW_SECONDS = 10.0
GLITCH_CHARS = "▓▒░█▌▐▄▀#@%&$01<>/\\|?*"
GLITCH_COLORS = ((0, 255, 255), (255, 0, 255), (160, 255, 0), (255, 255, 255))
DECRYPT_CHARS = "01#$%&*+=<>?/\\|░▒▓"
_BOX_CHARS = frozenset("─━│┃┌┐└┘├┤┬┴┼╭╮╯╰═║╔╗╚╝╠╣╦╩╬╒╓╕╖╘╙╛╜╞╟╡╢╤╥╧╨╪╫")
_STYLE_CACHE: dict = {}
_ALERT_CACHE: dict = {}
# VS Code-like ANSI palette: used to turn named colours ("red", "bright_cyan", ...) into real RGB before re-tinting them.
_TERM_THEME = None
if HAVE_RICH:
    _TERM_THEME = TerminalTheme((0, 0, 0), (204, 204, 204),
                                [(0, 0, 0), (205, 49, 49), (13, 188, 121), (229, 229, 16), (36, 114, 200), (188, 63, 188), (17, 168, 205), (229, 229, 229)],
                                [(102, 102, 102), (241, 76, 76), (35, 209, 139), (245, 245, 67), (59, 142, 234), (214, 112, 214), (41, 184, 219), (255, 255, 255)])

def parse_hex_color(v):
    m = re.fullmatch(r"#?([0-9a-fA-F]{6})", str(v).strip())
    if not m:
        return None
    n = int(m.group(1), 16)
    return (n >> 16 & 255, n >> 8 & 255, n & 255)

def cosmetics_now(now: float) -> dict:
    """slot -> shop item in effect right now: what is equipped, with a live preview laid over it."""
    out: dict = {}
    if not GAME["on"] or not STATE:
        return out
    c = STATE.get("coins")
    if isinstance(c, dict):
        for slot in COSMETIC_SLOTS:
            iid = c.get("equipped", {}).get(slot, "")
            it = GAME["smap"].get(iid)
            if it and iid in c.get("owned", {}):
                out[slot] = it
    if PREVIEW["item"]:
        it = GAME["smap"].get(PREVIEW["item"])
        if it and now < PREVIEW["until"]:
            out[it["type"]] = it
        else:
            PREVIEW["item"] = ""
    return out

def decrypt_active(now: float) -> bool:
    return "decrypt" in cosmetics_now(now) and CFG["fx"]

def cosmetics_animated(now: float) -> bool:
    """True while an equipped cosmetic is moving, so the main loop uses the faster frame rate."""
    if not CFG["fx"]:
        return False
    cos = cosmetics_now(now)
    if "neon" in cos or "glitch" in cos:
        return True
    return "decrypt" in cos and now - STATUS.t < 0.015 * len(STATUS.text) + 0.5

def _rgb_of(color, fg: bool = True):
    if color is None:
        return tuple(_TERM_THEME.foreground_color if fg else _TERM_THEME.background_color)
    return tuple(color.get_truecolor(_TERM_THEME, foreground=fg))

def _is_alert_red(r, g, b) -> bool:
    h, s, v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
    return s > 0.55 and v > 0.45 and (h < 0.045 or h > 0.955)

def _style_is_alert(style) -> bool:
    hit = _ALERT_CACHE.get(style)
    if hit is None:
        if len(_ALERT_CACHE) > 4000:
            _ALERT_CACHE.clear()
        hit = _ALERT_CACHE[style] = _is_alert_red(*_rgb_of(style.color if style else None))
    return hit

def _mix_rgb(a, b, t: float):
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))

def theme_rgb(rgb, spec: dict, shift: float, bg: bool = False):
    """Re-tint one colour for a theme. Brightness carries the hierarchy; hue comes from the theme."""
    r, g, b = rgb
    mode, cols = spec["mode"], spec["colors"]
    if mode == "cycle":
        h, s, v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
        if s < 0.12 or (not bg and _is_alert_red(r, g, b)):
            return rgb
        return tuple(int(x * 255) for x in colorsys.hsv_to_rgb((h + shift) % 1.0, s, v))
    if not bg and _is_alert_red(r, g, b):
        return rgb
    lum = (0.2126 * r + 0.7152 * g + 0.0722 * b) / 255
    if mode == "mono" or len(cols) < 2:
        base = cols[0]
    else:                                              # duo: warm hues take colour 1, cool hues colour 2, greys the optional colour 3
        h, s, _v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
        if s < 0.18:
            base = cols[2] if len(cols) > 2 else _mix_rgb(cols[1], (255, 255, 255), 0.5)
        else:
            base = cols[0] if (h < 0.17 or h > 0.78) else cols[1]
    k = (0.12 + 0.55 * lum ** 0.8) if bg else (0.22 + 0.78 * lum ** 0.75)
    k = min(1.0, k)
    return (int(base[0] * k), int(base[1] * k), int(base[2] * k))

def neon_rgb(rgb, pulse: float):
    """Saturate, lift the shadows and breathe: colours look lit from inside."""
    h, s, v = colorsys.rgb_to_hsv(rgb[0] / 255, rgb[1] / 255, rgb[2] / 255)
    if s > 0.12:
        s = min(1.0, s * 1.4 + 0.15)
    v = min(1.0, (v ** 0.45) * (0.93 + 0.07 * pulse))
    return tuple(int(x * 255) for x in colorsys.hsv_to_rgb(h, s, v))

def restyle(style, spec, neon: bool, pulse: float, shift: float):
    base = style if style is not None else Style()
    fg = _rgb_of(base.color, True)
    bgc = None if base.bgcolor is None or base.bgcolor.type == ColorType.DEFAULT else _rgb_of(base.bgcolor, False)
    alert = _is_alert_red(*fg)
    if spec:
        fg = theme_rgb(fg, spec, shift)
        if bgc:
            bgc = theme_rgb(bgc, spec, shift, bg=True)
    if neon and not alert:
        fg = neon_rgb(fg, pulse)
    new = Style(color=Color.from_rgb(*fg), bgcolor=Color.from_rgb(*bgc) if bgc else None, bold=True if (neon and not alert and not base.dim) else None)
    if spec and base.reverse and bgc is None:          # 'reverse' on default colours: keep the swap inside the theme
        new = new + Style(bgcolor=Color.from_rgb(0, 0, 0))
    return base + new

def _neon_border(seg, x: int, y: int, now: float, spec, fx_on: bool) -> list:
    """Box-drawing runs become glowing tubes: a colour wave travels along them (rainbow, or the theme's own colours)."""
    text, style = seg.text, seg.style
    t = now if fx_on else 0.0
    keep_bg = style.bgcolor if style else None
    out, i = [], 0
    while i < len(text):
        chunk, cx = text[i:i + 4], x + i
        wave = 0.5 + 0.5 * math.sin(cx * 0.11 + y * 0.3 - t * 3.2)
        if spec and spec["mode"] != "cycle":
            cols = spec["colors"]
            rgb = _mix_rgb(cols[0], cols[1], wave) if len(cols) > 1 and spec["mode"] == "duo" else tuple(int(c * (0.55 + 0.45 * wave)) for c in cols[0])
        else:
            rgb = tuple(int(c * 255) for c in colorsys.hsv_to_rgb((cx * 0.011 + y * 0.021 - t * 0.12) % 1.0, 1.0, 1.0))
        out.append(Segment(chunk, Style(color=Color.from_rgb(*rgb), bold=True, bgcolor=keep_bg)))
        i += 4
    return out

def _shift_line(line: list, dx: int, width: int) -> list:
    """Slide a rendered row sideways by dx cells (positive = right), keeping it exactly `width` cells wide."""
    if dx > 0:
        return [Segment(" " * dx)] + Segment.adjust_line_length(line, max(0, width - dx), pad=True)
    parts = list(Segment.divide(line, [-dx, width]))
    return Segment.adjust_line_length(parts[1] if len(parts) > 1 else [], width, pad=True)

class GlitchPlan:
    """What one glitch frame does. Built from a seed, so every redraw inside the same frame is identical."""

    def __init__(self, kinds, level: int, rng, width: int, height: int):
        self.rng, self.width = rng, width
        self.p = 0.05 + 0.05 * level                       # share of characters garbled on a corrupted row
        rows = lambda n: {rng.randrange(max(1, height)) for _ in range(n)}
        self.shift, self.split, self.corrupt, self.flash = {}, {}, set(), set()
        if "tear" in kinds:
            for _ in range(rng.randint(level + 1, level + 3)):
                y0, dx = rng.randrange(max(1, height)), rng.choice((-1, 1)) * rng.randint(2, 5 + 4 * level)
                for y in range(y0, y0 + rng.randint(1, 3)):
                    self.shift[y] = dx
        if "split" in kinds:
            for y in rows(2 * level + 1):
                self.split[y] = [rng.choice(GLITCH_COLORS) for _ in range(3)]
        if "corrupt" in kinds:
            self.corrupt = rows(2 * level)
        if "flash" in kinds and self.rng.random() < 0.5:
            self.flash = rows(2)

    def apply(self, line: list, y: int) -> list:
        if y in self.split:
            cols, x, out = self.split[y], 0, []
            for seg in line:
                if seg.control or not seg.text.strip():
                    out.append(seg)
                else:
                    band = min(2, x * 3 // max(1, self.width))
                    out.append(Segment(seg.text, (seg.style or Style()) + Style(color=Color.from_rgb(*cols[band]), bold=True)))
                x += seg.cell_length
            line = out
        if y in self.corrupt:
            out = []
            for seg in line:
                if seg.control or not seg.text.strip():
                    out.append(seg)
                    continue
                chars = list(seg.text)
                for i, ch in enumerate(chars):
                    if ch != " " and self.rng.random() < self.p and cell_len(ch) == 1:
                        chars[i] = self.rng.choice(GLITCH_CHARS)
                out.append(Segment("".join(chars), seg.style, seg.control))
            line = out
        if y in self.flash:
            line = [s if s.control else Segment(s.text, (s.style or Style()) + Style(reverse=True)) for s in line]
        dx = self.shift.get(y)
        if dx:
            line = _shift_line(line, dx, self.width)
        return line

def glitch_plan(now: float, item: dict, width: int, height: int):
    """Glitches arrive in short random bursts (a few frames each); None between bursts."""
    spec = item["spec"]
    level = spec["level"]
    period = (4.2, 2.9, 1.9)[level - 1]
    slot = int(now // period)
    seed = f"{STATE.get('seed', '')}|{item['id']}|{slot}"
    rng = random.Random(seed)
    start = slot * period + rng.uniform(0.15, max(0.2, period - 0.9))
    dur = rng.uniform(0.2, 0.32 + 0.1 * level)
    if not (start <= now < start + dur):
        return None
    return GlitchPlan(spec["kinds"], level, random.Random(f"{seed}|{int((now - start) / 0.08)}"), width, height)

class CosmeticFilter:
    """Wraps the finished screen: theme re-tint, neon glow and glitch bursts, in that order."""

    def __init__(self, inner, now: float):
        self.inner, self.now = inner, now

    def __rich_console__(self, console, options):
        lines = console.render_lines(self.inner, options, pad=True)
        try:
            lines = self._apply(lines, options.max_width)
        except Exception:                                  # cosmetics must never be able to take the dashboard down
            pass
        n = len(lines)
        for y, line in enumerate(lines):
            yield from line
            if y < n - 1:
                yield Segment.line()

    def _apply(self, lines: list, width: int) -> list:
        now, fx_on = self.now, CFG["fx"]
        cos = cosmetics_now(now)
        theme, glitch = cos.get("theme"), cos.get("glitch")
        spec = theme["spec"] if theme else None
        neon = "neon" in cos
        pulse = 0.5 + 0.5 * math.sin(now * 2.2) if (neon and fx_on) else 1.0
        npk = int(pulse * 4)
        cyc = int((now * 0.04 % 1.0) * 48) if (spec and spec["mode"] == "cycle" and fx_on) else 0
        tid = theme["id"] if theme else ""
        if len(_STYLE_CACHE) > 8000:
            _STYLE_CACHE.clear()

        def remap(style):
            k = (style, tid, neon, npk, cyc)
            hit = _STYLE_CACHE.get(k)
            if hit is None:
                hit = _STYLE_CACHE[k] = restyle(style, spec, neon, npk / 4.0, cyc / 48.0)
            return hit

        plan = glitch_plan(now, glitch, width, len(lines)) if (glitch and fx_on) else None
        out = []
        for y, line in enumerate(lines):
            if spec or neon:
                new, x = [], 0
                for seg in line:
                    if seg.control or not seg.text:
                        new.append(seg)
                        continue
                    if neon and seg.text.strip() and _BOX_CHARS.issuperset(seg.text.replace(" ", "")) and not _style_is_alert(seg.style):
                        new.extend(_neon_border(seg, x, y, now, spec, fx_on))
                    else:
                        new.append(Segment(seg.text, remap(seg.style), seg.control))
                    x += seg.cell_length
                line = new
            if plan:
                line = plan.apply(line, y)
            out.append(line)
        return out

def decrypt_status_text(now: float) -> Text:
    """The status line. With the Decrypt Status Line cosmetic, new messages scramble and then resolve left to right."""
    text = STATUS.text
    if not decrypt_active(now) or not text:
        return Text(text, style="yellow", no_wrap=True, overflow="ellipsis")
    age = now - STATUS.t
    resolved = int(max(0.0, age - 0.25) / 0.015)
    out = Text(no_wrap=True, overflow="ellipsis")
    out.append(text[:resolved], style="yellow")
    if resolved < len(text):
        frame = int(now * 18)
        scr = "".join(ch if (ch == " " or cell_len(ch) != 1) else DECRYPT_CHARS[(i * 7 + frame * 13) % len(DECRYPT_CHARS)]
                      for i, ch in enumerate(text[resolved:]))
        out.append(scr, style="bold green")
    return out

def glitch_live(now: float) -> bool:
    return CFG["fx"] and "glitch" in cosmetics_now(now)

# ---- frame-rate control ----------------------------------------------------
def anim_active(now: float) -> bool:
    """True while something on screen is moving, so the main loop should run at the faster frame rate."""
    if not CFG["fx"]:
        return False
    if cosmetics_animated(now) or now - COINANIM["t"] < 2.5:       # neon glow / glitch bursts / decrypting status / the "+N" coin tag
        return True
    if CFG["scanning"] or CFG["crt"] or SUPPORT["on"]:    # heartbeat trace scrolls / CRT band rolls / supporter sparkle
        return True
    if current_view()[0] == "radar" or hunting():
        return True
    a = XPANIM
    if a["disp"] is not None and now - a["gain_t"] < 4.0:
        return True
    return any(now - d.first < FLASH_SECONDS or d.ident.tier in ("alert", "possible")
               for d in DEVICES.values() if now - d.last <= CFG["stale"])

# ---- radar sweep -----------------------------------------------------------
RADAR_PERIOD = 4.2           # seconds per sweep
RADAR_TRAIL = 1.15           # radians of fading wedge behind the sweep line
RADAR_MAX_FT = 300.0
RADAR_RINGS_FT = (10, 30, 100, 300)
_WEDGE = [""] + [f"on rgb(0,{int(12 + 60 * i / 8)},{int(4 + 14 * i / 8)})" for i in range(9)]    # level 0 = no tint
_RING_FG = ["grey42", "grey42", "grey39", "grey50"]
_RADAR_CACHE = {"geom": {}, "rings": {}, "angle": {}}

def radar_frac(d_ft: float) -> float:
    """Distance -> 0..1 of the radar radius (log scale, so the 10-100 ft zone you care about gets the room)."""
    return min(1.0, math.log10(1 + max(0.0, d_ft) / 3.0) / math.log10(1 + RADAR_MAX_FT / 3.0))

def radar_angle(key: str) -> float:
    """Stable made-up bearing for a device. BLE has no direction, so this only keeps each blip from jumping around."""
    cache = _RADAR_CACHE["angle"]
    a = cache.get(key)
    if a is None:
        if len(cache) > 5000:
            cache.clear()
        a = cache[key] = int(hashlib.sha1(key.encode()).hexdigest()[:8], 16) / 0xFFFFFFFF * TWO_PI
    return a

def _radar_geom(rx: int, ry: int):
    """(x, y, angle) of every canvas cell inside the radar ellipse. Cells are about twice as tall as wide."""
    g = _RADAR_CACHE["geom"].get((rx, ry))
    if g is None:
        g = []
        for y in range(2 * ry + 1):
            dy = (y - ry) * 2.0
            for x in range(2 * rx + 1):
                dx = x - rx
                if dx * dx + dy * dy <= (rx + 0.5) ** 2:
                    g.append((x, y, math.atan2(dy, dx) % TWO_PI))
        _RADAR_CACHE["geom"] = {(rx, ry): g}          # keep only the current size
    return g

def _radar_rings(rx: int, ry: int):
    r = _RADAR_CACHE["rings"].get((rx, ry))
    if r is None:
        r = {}
        for ri, ft in enumerate(RADAR_RINGS_FT):
            R = radar_frac(ft) * rx
            steps = max(24, int(TWO_PI * R * 1.6))
            for s in range(steps):
                a = TWO_PI * s / steps
                r[(int(round(R * math.cos(a))), int(round(R * math.sin(a) / 2)))] = ri
        _RADAR_CACHE["rings"] = {(rx, ry): r}
    return r

def radar_label(dev) -> str:
    name = (KNOWN.renames.get(dev.mac) if KNOWN else None) or CFG_NAMES.get(dev.mac) or friendly_name(dev) or dev.ident.label or dev.mac[-8:]
    return clean(name, 14)

def radar_style(dev, now: float):
    """(glyph, colour) for a device: tier / known / category decides the look."""
    tier = dev.ident.tier
    if tier == "alert":
        return "◆", "bright_red"
    if tier == "possible":
        return "◈", "yellow"
    if dev.ident.known:
        return "★", "bright_green"
    return "●", CATEGORY_COLORS.get(dev.ident.category, "cyan")

def build_radar_view(size, now):
    """Sweeping radar: distance (from signal strength) is the radius, a rotating beam lights up each blip as it passes."""
    W, H = size
    devs = get_processed_devices(now)
    dist = {d.mac: est_distance_ft(d.ema, d.tx) for d in devs}
    side_w = 36 if W >= 104 else 0
    inner_w = W - 2 - side_w
    inner_h = H - 2 - 1                                 # panel border + the ring-count row
    ry = min((inner_h - 1) // 2, 24, (inner_w - 3) // 4)
    if ry < 3:
        return Panel(Text("Terminal too small for the radar. Enlarge the window or press v for another view.", style="dim"),
                     title="[bold]📡 Radar Sweep[/]", border_style="green", box=ROUNDED)
    rx = 2 * ry
    cw, chh, cx, cy = 2 * rx + 1, 2 * ry + 1, rx, ry
    sweeping = CFG["fx"]
    theta = ((now % RADAR_PERIOD) / RADAR_PERIOD) * TWO_PI

    ch = [[" "] * cw for _ in range(chh)]
    fg = [[""] * cw for _ in range(chh)]
    bg = [[0] * cw for _ in range(chh)]
    occupied = set()

    for x in range(cw):                                 # faint crosshair
        ch[cy][x], fg[cy][x] = "─", "grey23"
    for y in range(chh):
        ch[y][cx], fg[y][cx] = "│", "grey23"
    ch[cy][cx], fg[cy][cx] = "┼", "green"
    if sweeping:                                        # sweep wedge: tinted background fading behind the beam
        for x, y, phi in _radar_geom(rx, ry):
            delta = (theta - phi) % TWO_PI
            if delta < RADAR_TRAIL:
                lvl = int((1 - delta / RADAR_TRAIL) ** 1.6 * 8) + 1
                bg[y][x] = min(9, lvl)
    for (x, y), ri in _radar_rings(rx, ry).items():
        px, py = cx + x, cy + y
        if 0 <= px < cw and 0 <= py < chh:
            ch[py][px], fg[py][px] = "·", _RING_FG[ri]
    for ri, ft in enumerate(RADAR_RINGS_FT):            # ring labels just above the 12 o'clock point of each ring
        lab = f"{ft}ft"
        ly, lx = cy - int(round(radar_frac(ft) * rx / 2)) + 1, cx + 2
        if 0 <= ly < chh and lx + len(lab) <= cw:
            for k, c in enumerate(lab):
                ch[ly][lx + k], fg[ly][lx + k] = c, "grey50"

    # blips: far ones first so near ones draw on top
    blips = []
    for dev in sorted(devs, key=lambda d: -dist[d.mac]):
        R = max(2.0, radar_frac(dist[dev.mac]) * (rx - 1))
        ang = radar_angle(dev.ghost_id or dev.mac)
        x, y = cx + int(round(R * math.cos(ang))), cy + int(round(R * math.sin(ang) / 2))
        if not (0 <= x < cw and 0 <= y < chh):
            continue
        glyph, col = radar_style(dev, now)
        live = now - dev.last <= ACTIVE_WINDOW
        since = ((theta - ang) % TWO_PI) / TWO_PI * RADAR_PERIOD if sweeping else 0.0
        if not live:
            glyph, sty = "○", "dim " + col
        elif sweeping and since < 0.35:
            glyph, sty = "◉", "bold bright_white"
        elif sweeping and since < 1.6:
            sty = "bold " + col
        elif sweeping and since < 3.2:
            sty = col
        else:
            sty = col if not sweeping else "dim " + col
        if dev.ident.tier == "alert" and sweeping and live and int(now * 3) % 2:
            sty = "bold white"
        if hunting() and dev.mac == HUNT["mac"]:
            glyph, sty = ("✚", "bold bright_magenta") if int(now * 2.5) % 2 or not sweeping else ("✚", "bold white")
        ch[y][x], fg[y][x] = glyph, sty
        occupied.add((x, y))
        blips.append((dist[dev.mac], dev, x, y))

    blips.sort(key=lambda b: b[0])                      # label the closest few live devices
    for d_ft, dev, x, y in [b for b in blips if now - b[1].last <= ACTIVE_WINDOW][:6]:
        lab = radar_label(dev)
        for lx in (x + 2, x - 1 - len(lab)):
            if 0 <= lx and lx + len(lab) <= cw and 0 <= y < chh and not any((lx + k, y) in occupied for k in range(len(lab))):
                for k, c in enumerate(lab):
                    ch[y][lx + k], fg[y][lx + k] = c, "bold bright_white"
                    occupied.add((lx + k, y))
                break

    rows = []
    for y in range(chh):
        line = Text(no_wrap=True, overflow="crop")
        run, run_style = "", None
        for x in range(cw):
            st = (fg[y][x] + " " + _WEDGE[bg[y][x]]).strip()
            if st != run_style and run:
                line.append(run, style=run_style or None)
                run = ""
            run_style = st
            run += ch[y][x]
        if run:
            line.append(run, style=run_style or None)
        rows.append(line)

    summary = Text(no_wrap=True, overflow="ellipsis")
    lo = -1.0
    for hi, label in DIST_RINGS:
        n = sum(1 for d in devs if lo < dist[d.mac] <= hi)
        summary.append(f"{label} {n}", style="bright_white" if n else "dim")
        summary.append("  ·  ", style="dim")
        lo = hi
    summary.append(f"{len(devs)} in range", style="cyan")
    left = Panel(Group(summary, Align.center(Group(*rows), vertical="middle", height=max(1, inner_h))),
                 title="[bold]📡 Radar Sweep[/]", title_align="left", border_style="green", box=ROUNDED,
                 subtitle="distance from signal strength · angle is arbitrary (BLE has no bearing)")
    if not side_w:
        return left

    table = Table.grid(padding=(0, 1), expand=True)
    table.add_column(ratio=1, no_wrap=True, overflow="ellipsis")
    table.add_column(no_wrap=True, justify="right")
    live_near = [b for b in blips if now - b[1].last <= ACTIVE_WINDOW]
    for d_ft, dev, _, _ in live_near[:max(1, inner_h - 6)]:
        glyph, col = radar_style(dev, now)
        n = Text(no_wrap=True, overflow="ellipsis")
        n.append(glyph + " ", style=col)
        n.append(radar_label(dev), style=throb_text("bold", dev.ident.tier, now))
        table.add_row(n, Text(">300ft" if d_ft > 300 else f"{d_ft:.0f}ft", style="green" if d_ft <= 30 else "dim"))
    if not live_near:
        table.add_row(Text("no live devices", style="dim"), "")
    legend = Text(no_wrap=True, overflow="ellipsis")
    for g, c, name in (("◆", "bright_red", "alert"), ("◈", "yellow", "possible"), ("★", "bright_green", "known"), ("●", "cyan", "device")):
        legend.append(g + " ", style=c)
        legend.append(name + "  ", style="dim")
    side = Panel(Group(table, Text(""), legend), title="[bold]Nearest[/]", title_align="left", border_style="cyan", box=ROUNDED)
    root = Layout()
    root.split_row(Layout(left, ratio=1), Layout(side, size=side_w))
    return root

# ---- hunt sonar ------------------------------------------------------------
SONAR_LIFE = 1.7             # seconds an expanding ring lives

def build_sonar(now: float, rows: int, color: str, dev, r: float):
    """(Group of Text rows, width). Rings expand from the centre on every ping; the target dot flares as a ring passes it.
    Closer target = dot nearer the centre and pings come faster (the same clock as the beeps)."""
    ry = max(2, rows // 2)
    rx = 2 * ry
    cw, chh = 2 * rx + 1, 2 * ry + 1
    ch = [[" "] * cw for _ in range(chh)]
    fg = [[""] * cw for _ in range(chh)]
    for x in range(cw):
        ch[ry][x], fg[ry][x] = "─", "grey23"
    for y in range(chh):
        ch[y][rx], fg[y][rx] = "│", "grey23"
    d_ft = est_distance_ft(r, dev.tx)
    tR = max(2.0, radar_frac(d_ft) * (rx - 1))
    tang = radar_angle(dev.ghost_id or dev.mac)
    tx, ty = rx + int(round(tR * math.cos(tang))), ry + int(round(tR * math.sin(tang) / 2))
    flare = False
    for tp in list(HUNT["pings"]):
        age = now - tp
        if not (0.0 <= age < SONAR_LIFE):
            continue
        R = age / SONAR_LIFE * rx
        flare = flare or abs(R - tR) < 1.6
        glyph = "•" if age < 0.6 else "·"
        sty = f"bold {color}" if age < 0.9 else (color if age < 1.4 else f"dim {color}")
        steps = max(20, int(TWO_PI * R * 1.6))
        for s in range(steps):
            a = TWO_PI * s / steps
            x, y = rx + int(round(R * math.cos(a))), ry + int(round(R * math.sin(a) / 2))
            if 0 <= x < cw and 0 <= y < chh:
                ch[y][x], fg[y][x] = glyph, sty
    if 0 <= tx < cw and 0 <= ty < chh:
        ch[ty][tx], fg[ty][tx] = ("✹", "bold bright_white") if flare else ("●", f"bold {color}")
    ch[ry][rx], fg[ry][rx] = ("★", "bold bright_yellow") if HUNT["found"] else ("◉", "bold bright_white")
    out = []
    for y in range(chh):
        line = Text(no_wrap=True, overflow="crop")
        run, run_style = "", None
        for x in range(cw):
            st = fg[y][x]
            if st != run_style and run:
                line.append(run, style=run_style or None)
                run = ""
            run_style = st
            run += ch[y][x]
        if run:
            line.append(run, style=run_style or None)
        out.append(line)
    interval = 2.0 - 1.8 * HUNT["close"]
    out.append(Text(f"sonar · ping every {interval:.1f}s", style="dim", no_wrap=True, overflow="ellipsis"))
    return Group(*out), cw

def device_panel(title, color, devs, max_lines, now, subtitles, spin):
    grid = Table.grid(expand=True)
    grid.add_column(ratio=1, no_wrap=True, overflow="ellipsis")
    grid.add_column(no_wrap=True, justify="right")

    # Limit to a maximum of 5 devices and force 1 line per device
    cap = min(len(devs), max(1, max_lines))

    if not devs:
        grid.add_row(Text(f"scanning {spin}", style="dim cyan"), "")

    for dev in devs[:cap]:
        live = now - dev.last <= ACTIVE_WINDOW
        st = f"bold {color}" if live else "dim"
        nstyle, fresh = flash_style(dev, now, st)
        left = Text("✦ " if fresh else ("● " if live else "○ "),
                    style="bold bright_white" if fresh else ("bright_green" if live else "dim"))
        left.append(display_name(dev), style=throb_text(nstyle, dev.ident.tier, now) if not fresh else nstyle)
        grid.add_row(left, meter(dev, now, "bright_green" if live else "dim"))
        # Subtitle row omitted to keep each device strictly on a single line

    return Panel(grid, title=title, title_align="left", border_style=throb_border(color, worst_tier(devs[:cap]), now),
                 box=ROUNDED, padding=(0, 1))

FLOOD_KEEP = 1          # when one name shows up more than this many times, only the strongest FLOOD_KEEP stay visible
FLOOD_HIDDEN: dict = {}  # name -> how many weaker duplicates were hidden on the last refresh (for the "+N hidden" notes)

def flood_name(dev: Dev) -> str:
    """The name a device is listed under, minus the icon and the ghost tag."""
    return dev.name or dev.ident.label or ""

def flood_exempt(dev: Dev) -> bool:
    """Devices that must never be hidden by name-flood collapsing."""
    i = dev.ident
    return bool(i.known) or i.tier in ("alert", "possible", "known") or dev.mac == HUNT["mac"] \
        or dev.mac in CFG_NAMES or bool(KNOWN and dev.mac in KNOWN.renames)

def collapse_name_floods(devs: list) -> list:
    """When the same name appears more than FLOOD_KEEP times (e.g. dozens of 'Google Nearby device'
    ghosts), keep only the FLOOD_KEEP strongest signals and hide the weaker repeats."""
    groups = collections.defaultdict(list)
    for d in devs:
        n = flood_name(d)
        if n and not flood_exempt(d):
            groups[(d.ident.category, n)].append(d)
    FLOOD_HIDDEN.clear()
    hide = set()
    for (cat, name), members in groups.items():
        if len(members) <= FLOOD_KEEP:
            continue
        members.sort(key=lambda d: d.ema, reverse=True)
        extra = members[FLOOD_KEEP:]
        hide.update(d.mac for d in extra)
        FLOOD_HIDDEN[name] = FLOOD_HIDDEN.get(name, 0) + len(extra)
    return [d for d in devs if d.mac not in hide] if hide else devs

def flood_note(max_names: int = 3) -> str:
    """Short text for the views: which names had weaker repeats hidden."""
    if not FLOOD_HIDDEN or not CFG["dedup"]:
        return ""
    top = sorted(FLOOD_HIDDEN.items(), key=lambda kv: -kv[1])[:max_names]
    more = len(FLOOD_HIDDEN) - len(top)
    txt = ", ".join(f"{n} +{c}" for n, c in top) + (f", +{more} more names" if more > 0 else "")
    return f"{sum(FLOOD_HIDDEN.values())} weaker repeats hidden ({txt}) · d shows all"

def get_processed_devices(now, flood=True):
    """Filters stale devices and optionally deduplicates/collapses rotating MACs.
    flood=False skips the repeated-name collapsing (used by the stats counts)."""
    active = [d for d in DEVICES.values() if now - d.last <= CFG["stale"] and passes_signal(d, now)]
    active.sort(key=lambda d: d.last, reverse=True)

    if not CFG["dedup"]:
        FLOOD_HIDDEN.clear()
        return active

    seen_fps = {}
    collapsed = []
    for dev in active:
        if dev.kind in ("private-resolvable", "private-nonresolvable", "random") and dev.fp and dev.fp[0]:
            fp_key = (dev.ident.category, dev.ident.label, dev.fp)
            if fp_key in seen_fps:
                continue
            seen_fps[fp_key] = dev
        collapsed.append(dev)
    if flood:
        collapsed = collapse_name_floods(collapsed)
    return collapsed

def group_devices(now):
    groups, tactical, known = collections.defaultdict(list), [], {}
    processed = get_processed_devices(now)

    for dev in processed:
        i = dev.ident
        if i.known:
            known[i.known] = dev
            KNOWN.seen[i.known] = (dev.mac, dev.last)
        elif i.tier in ("alert", "possible"):
            tactical.append(dev)
        else:
            groups[i.category].append(dev)
    for g in groups.values():
        g.sort(key=lambda d: d.ema, reverse=True)
    return groups, tactical, known

# =============================================================================
# ADDITIONAL VIEW MODES & HELP
# =============================================================================
def build_compact_view(size, now):
    table = Table(title="[bold cyan]Compact Device List (Deduplicated)[/]", box=ROUNDED, expand=True)
    table.add_column("Status", width=8)
    table.add_column("Name / Label", ratio=2)
    table.add_column("Category", ratio=1)
    table.add_column("MAC", width=17)
    table.add_column("RSSI / Dist", width=16, justify="right")

    active_devs = get_processed_devices(now)
    active_devs.sort(key=lambda d: d.ema, reverse=True)

    for dev in active_devs[:max(1, size[1] - 8)]:
        live = now - dev.last <= ACTIVE_WINDOW
        status_col = "bright_green" if live else "dim"
        cat_col = CATEGORY_COLORS.get(dev.ident.category, "cyan")
        table.add_row(
            status_text(dev, now, live),
            Text(display_name(dev), style=throb_text(flash_style(dev, now, "bold")[0], dev.ident.tier, now)),
            Text(dev.ident.category, style=cat_col),
            Text(dev.mac, style="dim"),
            meter(dev, now, status_col)
        )
    return Panel(table, title="[bold]Compact View (Press 'v' to cycle views, 'd' to toggle dedup)[/]",
                 border_style=throb_border("cyan", worst_tier(active_devs), now), box=ROUNDED)

def build_tactical_view(size, now):
    _, tactical, known = group_devices(now)
    table = Table(title="[bold red]Tactical & Alert Focus View[/]", box=ROUNDED, expand=True)
    table.add_column("Tier", width=10)
    table.add_column("Device / Label", ratio=2)
    table.add_column("Vendor / Org", ratio=2)
    table.add_column("MAC", width=17)
    table.add_column("RSSI", width=10, justify="right")

    all_tactical = tactical + list(known.values())
    if not all_tactical:
        table.add_row("---", "No tactical or flagged devices detected yet.", "", "", "")
    for dev in all_tactical:
        tier_style = throb_text("bold red" if dev.ident.tier == "alert" else "bold yellow", dev.ident.tier, now)
        table.add_row(
            Text(dev.ident.tier.upper(), style=tier_style),
            Text(display_name(dev), style=flash_style(dev, now, "bold")[0]),
            Text(dev.ident.vendor or dev.ident.label, style="cyan"),
            Text(dev.mac, style="dim"),
            Text(f"{dev.ema:.0f} dBm", style="green")
        )
    return Panel(table, title="[bold]Tactical View (Press 'v' to cycle views)[/]",
                 border_style=throb_border("red", worst_tier(all_tactical), now), box=ROUNDED)

BASE_VIEWS = [("grid", "Standard Grid"), ("top5", "Top 5 Categories"), ("compact", "Compact List"),
              ("tactical", "Tactical / Alert Focus"), ("security", "Security Watch"),
              ("proximity", "Proximity Radar (closest first)"), ("radar", "Radar Sweep"), ("arrivals", "New Arrivals"),
              ("stats", "Statistics"), ("ghosts", "MAC Rotation (ghosts)"), ("known", "Known & Named Devices"),
              ("sensors", "Sensors (decoded readings)")]

def view_list() -> list:
    """Every selectable view: the base views, then one per dashboard category (including config-defined ones)."""
    return BASE_VIEWS + [(f"cat:{c[0]}", f"{c[1]} {c[2]}") for c in CATEGORIES]

def current_view():
    views = view_list()
    CFG["view_mode"] %= len(views)
    return views[CFG["view_mode"]]

def auto_tactical_tick():
    """If a tactical device was just flagged and auto-switch is on, jump to the tactical view.
    A running hunt or an open inspector isn't interrupted; you only get the status message then."""
    pend = AUTO["pending"]
    if pend is None:
        return
    AUTO["pending"] = None
    if not CFG["auto_tactical"]:
        return
    mac, tier, label = pend
    msg = f"🎯 {tier.upper()} device found: {clean(label, 40)} ({mac})"
    names = [v[0] for v in view_list()]
    if current_view()[0] == "tactical" and not any(CFG[f"show_{o}"] for o in OVERLAYS):
        STATUS.set(msg)
    elif hunting() or (CFG["show_inspect"] and tier != "alert"):
        STATUS.set(msg + " (not switching during hunt/inspect; press v / w for the tactical view)")
    else:
        CFG["view_mode"] = names.index("tactical")
        CFG["show_inspect"] = False                      # an ALERT overrides the inspector; only a running hunt is protected
        close_overlays()
        STATUS.set(msg + ": switched to Tactical view")

def close_overlays():
    for o in OVERLAYS:
        CFG[f"show_{o}"] = False

def build_category_view(size, now, key):
    """Full-screen list of every live device in one category, strongest signal first."""
    meta = next((c for c in CATEGORIES if c[0] == key), None)
    if meta is None:
        return Panel(Text(f"Unknown category '{key}'."), border_style="red", box=ROUNDED)
    _, icon, title, color = meta
    devs = [d for d in get_processed_devices(now) if d.ident.category == key]
    devs.sort(key=lambda d: d.ema, reverse=True)

    table = Table(box=ROUNDED, expand=True)
    table.add_column("Status", width=8, no_wrap=True)
    table.add_column("Name", ratio=2, no_wrap=True, overflow="ellipsis")
    table.add_column("Details", ratio=3, no_wrap=True, overflow="ellipsis")
    table.add_column("MAC", width=17, no_wrap=True, style="dim")
    table.add_column("RSSI / Dist", width=18, justify="right", no_wrap=True)
    table.add_column("Tracked", width=8, justify="right", no_wrap=True)

    if not devs:
        table.add_row("---", Text(f"No {title.lower()} devices in range.", style="dim"), "", "", "", "")
    cap = max(1, size[1] - 7)
    for dev in devs[:cap]:
        live = now - dev.last <= ACTIVE_WINDOW
        tier = dev.ident.tier
        name_style = "bold red" if tier == "alert" else "bold yellow" if tier == "possible" else "bold green" if tier == "known" else "bold"
        table.add_row(status_text(dev, now, live),
                      Text(display_name(dev), style=throb_text(flash_style(dev, now, name_style)[0], tier, now)),
                      Text(sub_text(dev)),
                      dev.mac,
                      meter(dev, now, "bright_green" if live else "dim"),
                      fmt_dur(now - dev.first, True))
    more = f"  (+{len(devs) - cap} more not shown)" if len(devs) > cap else ""
    return Panel(table, title=f"[bold {color}]{icon} {title} ({len(devs)})[/]{more}", title_align="left",
                 subtitle="v / ← → cycle views · w pick a view", border_style=throb_border(color, worst_tier(devs[:cap]), now), box=ROUNDED)

SECURITY_LEVELS = {
    "alert": ("ALERT", "bold red"), "possible": ("POSSIBLE", "bold yellow"), "follower": ("FOLLOWER", "bold red"),
    "watchlist": ("WATCHLIST", "bold magenta"), "notice": ("NOTICE", "cyan"),
}
SECURITY_ORDER = ["alert", "possible", "follower", "watchlist", "notice"]

def security_rows(now) -> list:
    """(level, device) for everything security-relevant, most severe first, then strongest signal."""
    rows = []
    for dev in get_processed_devices(now):
        i = dev.ident
        if KNOWN and dev.mac in KNOWN.trusted:
            continue
        if i.known and not i.known_alert:
            continue                                   # a known device you've marked as harmless
        tail = TAILS.get(dev.mac)
        if i.known and i.known_alert:
            level = "watchlist"
        elif i.tier == "alert":
            level = "alert"
        elif i.tier == "possible":
            level = "possible"
        elif tail and FOLLOW_RANK[tail.tier] >= 2:
            level = "follower"
        elif i.category in SECURITY_CATS:
            level = "notice"
        else:
            continue
        rows.append((level, dev))
    rows.sort(key=lambda r: (SECURITY_ORDER.index(r[0]), -r[1].ema))
    return rows

def build_security_view(size, now):
    """One screen for everything security-related: tactical/ALPR/drone flags, followers, watchlist, pentest gear, trackers."""
    rows = security_rows(now)
    counts = collections.Counter(level for level, _ in rows)

    summary = Text(no_wrap=True, overflow="ellipsis")
    for level in SECURITY_ORDER:
        label, style = SECURITY_LEVELS[level]
        n = counts.get(level, 0)
        summary.append(f"{label} {n}", style=style if n else "dim")
        summary.append("  ·  ", style="dim")
    summary.append("watching: " + ", ".join(sorted(c.replace("_", " ") for c in SECURITY_CATS)), style="dim")

    table = Table(box=ROUNDED, expand=True)
    table.add_column("Level", width=10, no_wrap=True)
    table.add_column("Device", ratio=2, no_wrap=True, overflow="ellipsis")
    table.add_column("Why flagged", ratio=3, no_wrap=True, overflow="ellipsis")
    table.add_column("MAC", width=17, no_wrap=True, style="dim")
    table.add_column("RSSI / Dist", width=18, justify="right", no_wrap=True)

    if not rows:
        table.add_row("---", Text("Nothing security-relevant in range.", style="dim"), "", "", "")
    cap = max(1, size[1] - 8)
    for level, dev in rows[:cap]:
        label, style = SECURITY_LEVELS[level]
        i = dev.ident
        if level == "follower":
            tail = TAILS[dev.mac]
            why = f"close to you for {fmt_dur(tail.near_s, True)} across places"
        elif level == "watchlist":
            why = f"known-devices watchlist: {i.known}"
        else:
            why = (clean(i.reasons[0], 70) if i.reasons else "") or i.label or i.category.replace("_", " ")
        live = now - dev.last <= ACTIVE_WINDOW
        table.add_row(Text(label, style=throb_text(style, "alert" if level in ("alert", "follower") else "possible" if level == "possible" else "", now)),
                      Text(display_name(dev), style=flash_style(dev, now, style if level != "notice" else "bold")[0]),
                      Text(why), dev.mac, meter(dev, now, "bright_green" if live else "dim"))
    more = f"  (+{len(rows) - cap} more not shown)" if len(rows) > cap else ""
    hot = any(counts.get(k) for k in ("alert", "follower", "watchlist"))
    return Panel(Group(summary, table), title=f"[bold]🛡 Security Watch ({len(rows)})[/]{more}", title_align="left",
                 subtitle="v / ← → cycle views · f follower detail · c inspect",
                 border_style=throb_border("red" if hot else "yellow" if rows else "green",
                                           "alert" if hot else "possible" if counts.get("possible") else "", now),
                 box=ROUNDED)

VIEW_HINT = "v / ← → cycle views · w pick a view"
RANK_EXCLUDE = {"other", "anonymous", "tactical"}      # not counted as "popular" categories

def cat_meta(key: str):
    """(icon, title, colour) for a category key, with a fallback for 'tactical' / unknown keys."""
    if key == "tactical":
        return "🎯", "TACTICAL / FLAGGED", "red"
    c = next((c for c in CATEGORIES if c[0] == key), None)
    return (c[1], c[2], c[3]) if c else ("🔹", key.replace("_", " ").upper(), "cyan")

def bar_table(items, cap: int, style: str = "cyan", bar_w: int = 14) -> Table:
    """items = [(label, count)] -> label | bar | count rows, scaled to the biggest count."""
    g = Table.grid(padding=(0, 1), expand=True)
    g.add_column(ratio=1, no_wrap=True, overflow="ellipsis")
    g.add_column(no_wrap=True)
    g.add_column(justify="right", no_wrap=True)
    top = max((n for _, n in items), default=0) or 1
    if not items:
        g.add_row(Text("nothing yet", style="dim"), "", "")
    for label, n in items[:max(1, cap)]:
        g.add_row(Text(str(label)), mini_bar(n / top, bar_w, style), str(n))
    return g

def cell_layout(cells, cols: int) -> Layout:
    n_rows = math.ceil(len(cells) / cols)
    body = Layout()
    rows = [Layout(name=f"r{i}") for i in range(n_rows)]
    body.split_column(*rows)
    for i, row in enumerate(rows):
        row.split_row(*[Layout(c) for c in cells[i * cols:(i + 1) * cols]])
    return body

def build_top_categories_view(size, now):
    """The five categories with the most devices right now, each as a live panel, plus a summary cell."""
    W, H = size
    spin = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"[int(now * 8) % 10]
    devs = get_processed_devices(now)
    by_cat = collections.defaultdict(list)
    for d in devs:
        by_cat[d.ident.category].append(d)
    order = {c[0]: n for n, c in enumerate(CATEGORIES)}
    ranked = sorted((k for k in by_cat if k not in RANK_EXCLUDE and k in order), key=lambda k: (-len(by_cat[k]), order[k]))
    top = ranked[:5]
    cols = 3 if W >= 150 else 2 if W >= 100 else 1
    n_rows = math.ceil(6 / cols)
    lines = max(1, H // n_rows - 2)
    cells = []
    for rank, key in enumerate(top, 1):
        icon, title, color = cat_meta(key)
        group = sorted(by_cat[key], key=lambda d: d.ema, reverse=True)
        cells.append(device_panel(f"[bold {color}]#{rank} {icon} {title} ({len(group)})[/]", color, group, lines, now, True, spin))
    while len(cells) < 5:
        cells.append(Panel(Text("no more active categories", style="dim"), title=f"[dim]#{len(cells) + 1}[/]",
                           border_style="grey30", box=ROUNDED))
    in_top = sum(len(by_cat[k]) for k in top)
    g = kv_table()
    g.add_row("In range", Text(str(len(devs)), style="bold"))
    g.add_row("In top 5", Text(str(in_top)))
    g.add_row("Other cats", Text(str(sum(len(by_cat[k]) for k in ranked[5:]))))
    g.add_row("Unclassified", Text(str(len(by_cat.get("other", [])) + len(by_cat.get("anonymous", [])))))
    g.add_row("Flagged", Text(str(len(by_cat.get("tactical", []))), style="red" if by_cat.get("tactical") else "dim"))
    cells.append(Panel(g, title="[bold]📊 Everything else[/]", title_align="left", border_style="grey50", box=ROUNDED, padding=(0, 1)))
    return cell_layout(cells, cols)

DIST_RINGS = [(10, "≤10 ft"), (30, "10-30 ft"), (100, "30-100 ft"), (float("inf"), ">100 ft")]

def build_proximity_view(size, now):
    """Every live device ordered by estimated distance, with a ring summary."""
    devs = get_processed_devices(now)
    dist = {d.mac: est_distance_ft(d.ema, d.tx) for d in devs}
    # order by smoothed signal strength (same key as the closeness bar), distance only breaks ties
    devs.sort(key=lambda d: (-d.ema, dist[d.mac]))
    summary = Text(no_wrap=True, overflow="ellipsis")
    lo = -1.0
    for hi, label in DIST_RINGS:
        n = sum(1 for d in devs if lo < dist[d.mac] <= hi)
        summary.append(f"{label} {n}", style="bright_white" if n else "dim")
        summary.append("  ·  ", style="dim")
        lo = hi
    summary.append("distances are rough estimates from signal strength", style="dim")
    fn = flood_note()
    if fn:
        summary.append("\n" + fn, style="yellow")
    table = Table(box=ROUNDED, expand=True)
    table.add_column("Status", width=8, no_wrap=True)
    table.add_column("Name", ratio=2, no_wrap=True, overflow="ellipsis")
    table.add_column("Category", ratio=1, no_wrap=True, overflow="ellipsis")
    table.add_column("Closeness", width=22, no_wrap=True)
    table.add_column("Distance", width=9, justify="right", no_wrap=True)
    table.add_column("", width=2, no_wrap=True)
    if not devs:
        table.add_row("---", Text("No devices in range.", style="dim"), "", "", "", "")
    for dev in devs[:max(1, size[1] - (9 if fn else 8))]:
        live = now - dev.last <= ACTIVE_WINDOW
        col = "green" if dev.ema >= -67 else "yellow" if dev.ema >= -80 else "red"
        d_ft = dist[dev.mac]
        sym, tcol = trend(dev, now)
        table.add_row(status_text(dev, now, live),
                      Text(display_name(dev), style=throb_text(flash_style(dev, now, "bold")[0], dev.ident.tier, now)),
                      Text(dev.ident.category.replace("_", " "), style=CATEGORY_COLORS.get(dev.ident.category, "cyan")),
                      mini_bar(max(0.0, min(1.0, (dev.ema + 100) / 55)), 20, col),
                      ">300ft" if d_ft > 300 else f"{d_ft:.1f}ft",
                      Text(sym, style=tcol))
    return Panel(Group(summary, table), title="[bold]📡 Proximity Radar[/]", title_align="left",
                 subtitle=VIEW_HINT, border_style=throb_border("green", worst_tier(devs), now), box=ROUNDED)

ARRIVAL_WINDOW = 300.0

def build_arrivals_view(size, now):
    """Devices first heard within the last few minutes, newest first (rotations of an already-linked device are skipped when dedup is on)."""
    rows = []
    for d in DEVICES.values():
        if now - d.first > ARRIVAL_WINDOW or not passes_signal(d, now):
            continue
        g = GHOSTS.get(d.ghost_id)
        if CFG["dedup"] and g and len(g.macs) > 1 and g.macs[0] != d.mac:
            continue
        rows.append(d)
    rows.sort(key=lambda d: d.first, reverse=True)
    table = Table(box=ROUNDED, expand=True)
    table.add_column("Arrived", width=10, no_wrap=True)
    table.add_column("Status", width=8, no_wrap=True)
    table.add_column("Name", ratio=2, no_wrap=True, overflow="ellipsis")
    table.add_column("Details", ratio=3, no_wrap=True, overflow="ellipsis")
    table.add_column("RSSI / Dist", width=18, justify="right", no_wrap=True)
    if not rows:
        table.add_row("---", "", Text(f"Nothing new in the last {fmt_dur(ARRIVAL_WINDOW, True)}.", style="dim"), "", "")
    for dev in rows[:max(1, size[1] - 8)]:
        live = now - dev.last <= ACTIVE_WINDOW
        tier = dev.ident.tier
        style = "bold red" if tier == "alert" else "bold yellow" if tier == "possible" else "bold"
        table.add_row(f"{fmt_dur(now - dev.first, True)} ago",
                      Text("● LIVE" if live else "○ GONE", style="bright_green" if live else "dim"),
                      Text(display_name(dev), style=style), Text(sub_text(dev)),
                      meter(dev, now, "bright_green" if live else "dim"))
    note = ("  (everything is new during the first minutes of a session)" if SESSION["scan_seconds"] < ARRIVAL_WINDOW else "")
    return Panel(table, title=f"[bold]🆕 New Arrivals, last {fmt_dur(ARRIVAL_WINDOW, True)} ({len(rows)})[/]{note}",
                 title_align="left", subtitle=VIEW_HINT, border_style="bright_cyan", box=ROUNDED)

def build_stats_view(size, now):
    """Dashboard of what's around: category mix, signal spread, address types, vendors, session numbers."""
    W, H = size
    devs = get_processed_devices(now, flood=False)
    cols = 3 if W >= 150 else 2 if W >= 100 else 1
    n_rows = math.ceil(5 / cols)
    cap = max(1, H // n_rows - 2)

    def pan(title, body, color="cyan"):
        return Panel(body, title=f"[bold]{title}[/]", title_align="left", border_style=color, box=ROUNDED, padding=(0, 1))

    cat_n = collections.Counter(d.ident.category for d in devs)
    cat_items = sorted(((f"{cat_meta(k)[0]} {k.replace('_', ' ')}", n) for k, n in cat_n.items()), key=lambda x: -x[1])
    bins = [("strong ≥ -55", -55, 0), ("good -55…-67", -67, -55), ("fair -67…-80", -80, -67),
            ("weak -80…-90", -90, -80), ("faint < -90", -200, -90)]
    sig_items = [(label, sum(1 for d in devs if lo <= d.ema < hi + (1 if hi == 0 else 0))) for label, lo, hi in bins]
    addr_items = sorted(collections.Counter(d.ident.addr_type for d in devs).items(), key=lambda x: -x[1])
    vend = collections.Counter(clean(d.ident.vendor, 24) for d in devs if d.ident.vendor)
    ven_items = vend.most_common(max(1, cap))
    linked = [g for g in GHOSTS.values() if len(g.macs) > 1]
    s = kv_table()
    s.add_row("Scanned", Text(fmt_dur(SESSION["scan_seconds"])))
    s.add_row("Seen total", Text(str(len(SEEN))))
    s.add_row("In range", Text(str(len(devs))))
    s.add_row("Packets", Text(f"{STATS['packets']}  ({STATS['pps']:.0f}/s)"))
    s.add_row("Ghost IDs", Text(f"{len(GHOSTS)} tracked · {len(linked)} with rotations"))
    s.add_row("Signal filter", Text("off" if CFG["min_rssi"] is None else f"≥ {CFG['min_rssi']} dBm ({hidden_count(now)} hidden)"))
    if all_ignore_name_patterns():
        s.add_row("Name ignore", Text(f"{len(all_ignore_name_patterns())} pattern(s) · {len(NAME_IGNORED_MACS)} address(es) hidden"))
    cells = [pan("📊 Category mix", bar_table(cat_items, cap, "cyan")),
             pan("📶 Signal strength", bar_table(sig_items, cap, "green")),
             pan("🔗 Address types", bar_table(addr_items, cap, "magenta")),
             pan("🏷 Top vendors", bar_table(ven_items, cap, "yellow")),
             pan("🖥 Session", s, "grey50")]
    return cell_layout(cells, cols)

def build_ghosts_view(size, now):
    """Clusters of rotating private addresses that look like the same physical device."""
    clusters = sorted((g for g in GHOSTS.values() if len(g.macs) > 1), key=lambda g: (-g.rotations, -g.last))
    table = Table(box=ROUNDED, expand=True)
    table.add_column("Ghost", width=9, no_wrap=True, style="dim")
    table.add_column("Device", ratio=2, no_wrap=True, overflow="ellipsis")
    table.add_column("Rotations", width=9, justify="right", no_wrap=True)
    table.add_column("Current MAC", width=17, no_wrap=True)
    table.add_column("Earlier MACs", ratio=3, no_wrap=True, overflow="ellipsis", style="dim")
    table.add_column("Last heard", width=10, justify="right", no_wrap=True)
    if not clusters:
        table.add_row("---", Text("No rotations linked yet. Private addresses change about every 15 minutes.", style="dim"), "", "", "", "")
    for g in clusters[:max(1, size[1] - 8)]:
        cur = g.macs[-1]
        dev = DEVICES.get(cur)
        live = dev is not None and now - dev.last <= ACTIVE_WINDOW
        table.add_row(g.id, Text(display_name(dev) if dev else "(gone)", style="bold" if live else "dim"),
                      str(g.rotations), cur, ", ".join(g.macs[max(0, len(g.macs) - 4):-1]),
                      f"{fmt_dur(now - g.last, True)} ago")
    sub = f"{len(GHOSTS)} identities tracked · matches are probabilistic (advertisement shape + timing + signal), not certain"
    return Panel(table, title=f"[bold]👻 MAC Rotation ({len(clusters)} linked devices)[/]", title_align="left",
                 subtitle=sub, border_style="grey62", box=ROUNDED)

def build_known_view(size, now):
    """Devices you've named, flagged, or put in the known-devices file, plus entries not heard this session."""
    rows, matched = [], set()
    for d in DEVICES.values():
        i = d.ident
        if i.known:
            src, label = ("watchlist" if i.known_alert else "known device"), i.known
            if KNOWN:
                KNOWN.seen[i.known] = (d.mac, d.last)
        elif KNOWN and d.mac in KNOWN.renames:
            src, label = "renamed", KNOWN.renames[d.mac]
        elif d.mac in CFG_NAMES:
            src, label = "config name", CFG_NAMES[d.mac]
        elif ghost_alias(d):
            src, label = "ghost-linked", ghost_alias(d)
        else:
            continue
        matched.add(label)
        rows.append((0 if now - d.last <= ACTIVE_WINDOW else 1, -d.last, src, label, d))
    rows.sort(key=lambda r: (r[0], r[1]))
    table = Table(box=ROUNDED, expand=True)
    table.add_column("Status", width=11, no_wrap=True)
    table.add_column("Name", ratio=2, no_wrap=True, overflow="ellipsis")
    table.add_column("Source", width=13, no_wrap=True)
    table.add_column("MAC", width=17, no_wrap=True, style="dim")
    table.add_column("RSSI / Dist", width=18, justify="right", no_wrap=True)
    table.add_column("Last heard", width=10, justify="right", no_wrap=True)
    cap = max(1, size[1] - 8)
    for _, _, src, label, d in rows[:cap]:
        live = now - d.last <= ACTIVE_WINDOW
        table.add_row(Text("● LIVE" if live else "○ gone", style="bright_green" if live else "dim"),
                      Text(f"{CATEGORY_ICONS.get(d.ident.category, '🔌')} {label}", style="bold" if live else "dim"),
                      Text(src, style="magenta" if src == "watchlist" else "cyan"), d.mac,
                      meter(d, now, "bright_green" if live else "dim"), f"{fmt_dur(now - d.last, True)} ago")
    unseen = []
    for e in (KNOWN.entries if KNOWN else []):
        if e.get("label") in matched:
            continue
        mac = e.get("mac")
        mac = (mac[0] if isinstance(mac, list) and mac else mac) or "-"
        unseen.append((e.get("label", "?"), "watchlist" if e.get("alert", True) else "known device", str(mac)))
    room = cap - len(rows[:cap])
    for label, src, mac in unseen[:max(0, room)]:
        table.add_row(Text("– not heard", style="dim"), Text(label, style="dim"), Text(src, style="dim"), mac, "", "")
    if not rows and not unseen:
        table.add_row("---", Text("Nothing named or known yet. Press r to rename a device.", style="dim"), "", "", "", "")
    live_n = sum(1 for r in rows if r[0] == 0)
    return Panel(table, title=f"[bold]⭐ Known & Named Devices ({live_n} live · {len(rows)} heard · {len(unseen)} not heard)[/]",
                 title_align="left", subtitle=VIEW_HINT + " · r rename · x trust tracker", border_style="green", box=ROUNDED)

def build_sensors_view(size, now):
    """Every device broadcasting readings we can decode (thermometers, beacons with sensors, door/motion sensors...)."""
    devs = [d for d in DEVICES.values() if d.sensor and now - d.last <= SENSOR_STALE and passes_signal(d, now)]
    devs.sort(key=lambda d: d.ema, reverse=True)
    table = Table(box=ROUNDED, expand=True)
    table.add_column("Status", width=8, no_wrap=True)
    table.add_column("Name", ratio=2, no_wrap=True, overflow="ellipsis")
    table.add_column("Type", ratio=1, no_wrap=True, overflow="ellipsis")
    table.add_column("Readings", ratio=3, no_wrap=True, overflow="ellipsis")
    table.add_column("Signal", width=12, justify="right", no_wrap=True)
    if not devs:
        table.add_row("---", Text("No decodable sensors heard yet (BTHome, ATC/PVVX, Ruuvi, Govee H5074/H5075).", style="dim"), "", "", "")
    for d in devs[:max(1, size[1] - 8)]:
        live = now - d.last <= ACTIVE_WINDOW
        sn = d.sensor
        reads = "  ".join(f"{k} {v}" for k, v in sn["vals"]) or sn.get("summary", "")
        table.add_row(status_text(d, now, live), Text(display_name(d, sensor=False)), Text(sn["fmt"], style="cyan"),
                      Text(reads, style="bright_white" if live else "dim"),
                      f"{d.ema:.0f} dBm")
    return Panel(table, title=f"[bold]🌡 Sensors ({len(devs)} decoded)[/]", title_align="left",
                 subtitle=VIEW_HINT, border_style="green", box=ROUNDED)

EXTRA_VIEWS = {"top5": build_top_categories_view, "proximity": build_proximity_view, "radar": build_radar_view, "arrivals": build_arrivals_view,
               "stats": build_stats_view, "ghosts": build_ghosts_view, "known": build_known_view,
               "sensors": build_sensors_view}

def build_help_panel(size):
    table = Table(box=None, show_header=False, expand=True, padding=(0, 1))
    table.add_column(style="bold yellow", width=13, no_wrap=True)
    table.add_column(style="cyan", width=18, no_wrap=True)
    table.add_column(style="dim", ratio=1, no_wrap=True, overflow="ellipsis")
    for k, a, d in [
        ("s / S", "Toggle Scanning", "Start or pause BLE scanning (paused time isn't counted)."),
        ("m / M", "Toggle Mute", "Mute or unmute sounds, alerts and hunt beeps."),
        ("n / N", "Notify Sound", "Cycle the new-device sound: notify, notify2, notify3, off. N goes back; plays a preview."),
        ("z / Z", "Toggle Effects", "Celebration cards plus new-device flash, alert pulse, radar sweep, hunt sonar, heartbeat, XP shimmer."),
        ("o / O", "CRT Scanlines", "Dim every second row with a slow rolling refresh band (toggle)."),
        ("Space", "Skip Effect", "Skip the celebration animation that is currently on screen."),
        ("d / D", "Toggle Dedup", "Collapse rotating privacy MACs (auto-linked by fingerprint; 👻×N = rotations seen) and hide weaker repeats when one name shows up more than 3 times."),
        ("[ / ]", "Signal Filter", "Loosen / tighten the minimum signal: Off, -90, -80, -70, -60, -50 dBm."),
        ("l / L", "Set Signal Limit", "Type an exact minimum in dBm (e.g. -75). Blank or 0 turns the filter off."),
        ("a / A", "Alerts Bypass", "Alerts, known devices and the hunted device ignore the filter (toggle)."),
        ("r / R", "Rename Device", "Pick a device from a list (or type a MAC) and name it permanently."),
        ("i / I", "Ignore Device", "Permanently hide a device by MAC or by name (exact, wildcards like Galaxy*, or re:regex). -text undoes, list shows."),
        ("f / F", "Follower Watch", "Trackers that stay near you across places. Alerts pop up on their own."),
        ("x / X", "Trust Tracker", "Mark a tracker in Follower Watch as yours to stop its alerts."),
        ("g/G  e/E", "Hunt Mode", "g: pick a device to find / reopen the meter. e: end hunt (in hunt view)."),
        ("c / Enter", "Inspect Device", "Pick a device for details (identity, signal, history). c closes; Enter picks another."),
        ("k / K", "Classic Bluetooth", "Toggle classic (BR/EDR) discovery: finds older speakers, car stereos, headsets and discoverable phones. Linux only."),
        ("y / Y", "Connect to Device", "In the inspector: connect to that one device and read its model, firmware, battery and services (read-only, no pairing)."),
        ("v / → / ←", "Cycle Views", "Grid, top 5, compact, tactical, security, proximity, radar, arrivals, stats, ghosts, known, sensors, then each category. V goes back."),
        ("w / W", "Pick a View", "Choose any view (top 5, security, proximity, a single category...) from a numbered list."),
        ("p / P", "Player Profile", "Level, daily quests, bounties, achievements, titles. p closes."),
        ("y / Y", "Missions", "With the inspector closed: timed challenges with a countdown (e.g. 5 vendors in 3 min). 1-9 starts one, 0 abandons, y closes."),
        ("← → ↑ ↓ j k", "Profile Nav", "While the profile is open: ←/→ change page, ↑/↓ or j/k scroll."),
        ("t / T", "Titles & Name", "Equip an unlocked title or change your player name."),
        ("e / E", "Coin Exchange", "Spend Intel Coins on themes, neon mode, glitch effects. pN previews. (In the hunt view, e ends the hunt.)"),
        ("b / B", "Guide / Tutorial", "How every feature works and how to play the game. ←/→ pages, ↑/↓ scroll, 1-9 jump, b closes."),
        ("u / U", "Auto Tactical", "Toggle: jump to the Tactical view whenever a new alert/possible tactical device is found (saved)."),
        ("$", "Support the Dev", "Donate via PayPal, then enter the unlock code for a sparkling name and a gold SUPPORTER badge."),
        ("h / H / ?", "Toggle Help", "Show or hide this panel."),
        ("q / Q / Esc", "Quit", "Stop scanning and exit."),
    ]:
        table.add_row(k, a, d)
    return Panel(table, title="[bold]Help & Shortcuts (Press 'h' to return)[/]", border_style="cyan", box=ROUNDED)

def mini_bar(frac: float, width: int, style: str) -> Text:
    filled = int(width * max(0.0, min(1.0, frac)))
    t = Text(no_wrap=True)
    t.append("█" * filled, style=style)
    t.append("░" * (width - filled), style="grey30")
    return t

FOLLOW_STYLE = {"": ("tracking", "dim"), "watch": ("WATCH", "yellow"), "suspect": ("SUSPECT", "bold yellow"), "alert": ("ALERT", "bold red")}

def build_follow_panel(size):
    now = time.time()
    table = Table(box=ROUNDED, expand=True)
    table.add_column("#", width=3, justify="right", style="bold yellow")
    table.add_column("Level", width=8, no_wrap=True)
    table.add_column("Tracker", ratio=3, no_wrap=True, overflow="ellipsis")
    table.add_column("MAC", width=17, no_wrap=True, style="dim")
    table.add_column("Near you", width=9, justify="right", no_wrap=True)
    table.add_column("Places", width=6, justify="center", no_wrap=True)
    table.add_column("Signal", ratio=2, no_wrap=True, overflow="ellipsis")
    rows = follow_rows()
    if not rows:
        table.add_row("", "---", "No tracker has stayed close to you yet.", "", "", "", "")
    for n, t in enumerate(rows[:max(1, size[1] - 8)], 1):
        dev = DEVICES.get(t.mac)
        live = dev is not None and now - dev.last <= ACTIVE_WINDOW
        sig = f"● {dev.ema:.0f} dBm" if live else f"○ gone {fmt_dur(now - t.last, True)}"
        label, style = FOLLOW_STYLE[t.tier]
        places = sum(1 for k, sec in t.locs.items() if k >= 0 and sec >= FOLLOW["min_loc_s"])
        table.add_row(str(n), Text(label, style=style), Text(t.label or "Tracker"), t.mac, fmt_dur(t.near_s), str(places),
                      Text(sig, style="green" if live else "dim"))
    sub = (f"Places are inferred from changes in nearby fixed devices (no GPS): {len(SCENE['locs'])} recognised. "
           f"x = mark one as yours.")
    return Panel(table, title="[bold]Follower Watch (Press 'f' to return)[/]", subtitle=sub,
                 border_style="red" if follow_alerts() else "yellow", box=ROUNDED)

def sparkline(dev, now: float, span: float = 20.0, width: int = 40) -> Text:
    bins = [[] for _ in range(width)]
    for t, r in dev.hist:
        age = now - t
        if 0 <= age < span:
            bins[width - 1 - int(age / span * width)].append(r)
    out = Text(no_wrap=True)
    for b in bins:
        if not b:
            out.append(" ")
        else:
            v = max(-100.0, min(-40.0, sum(b) / len(b)))
            out.append("▁▂▃▄▅▆▇█"[int((v + 100) / 60 * 7.999)], style="cyan")
    return out

def build_hunt_panel(size):
    now = time.time()
    title = "[bold]Hunt Mode (Press 'g' to return, 'e' to end the hunt)[/]"
    if not hunting():
        return Panel(Text("No active hunt. Press g from any screen to pick a device to find."), title=title,
                     border_style="magenta", box=ROUNDED)
    dev = DEVICES.get(HUNT["mac"])
    rows = [Text(f"Target: {display_name(dev) if dev else HUNT['mac']}", style="bold"),
            Text(f"{HUNT['mac']}" + (f"  ·  {sub_text(dev)}" if dev else ""), style="dim"), Text("")]
    sonar_args = None
    if dev is None or now - dev.last > 3.0:
        gone = "waiting for the target to advertise…" if dev is None else f"signal lost (last heard {fmt_dur(now - dev.last, True)} ago)"
        rows.append(Text(gone, style="yellow"))
        if dev is not None and dev.kind in ("private-resolvable", "private-nonresolvable", "random"):
            rows.append(Text("This device uses a rotating address; the hunt can't follow it once it changes.", style="dim"))
    else:
        r = fast_rssi(dev, now) or dev.ema
        label, col = hunt_temp(r)
        sonar_args = (dev, r, col)
        arrow, acol = hunt_trend(dev, now)
        bw = max(10, min(50, size[0] - 24))
        bar = mini_bar(max(0.0, min(1.0, (r + 100) / 55)), bw, col)
        d_ft = est_distance_ft(r, dev.tx)
        if HUNT["found"]:
            rows.append(Text("★  TARGET LOCATED  ★", style="bold bright_yellow"))
        else:
            rows.append(Text(label, style=f"bold {col}"))
        rows += [bar, Text(f"{r:.0f} dBm   ~{'>300' if d_ft > 300 else f'{d_ft:.0f}'} ft   ", style=col),
                 Text(arrow, style=acol), Text("")]
        rows.append(sparkline(dev, now, 20.0, bw))
        rows.append(Text("last 20 seconds", style="dim"))
        if not HUNT["found"] and HUNT["hot_since"]:
            rows.append(Text(f"Hold it… {max(0.0, HUNT_HOLD - (now - HUNT['hot_since'])):.1f}s", style="bright_yellow"))
    rows += [Text(""), Text(f"Elapsed {fmt_dur(now - HUNT['start'])}   ·   best signal {HUNT['best']:.0f} dBm", style="dim"),
             Text(f"Located at {HUNT_FOUND_RSSI} dBm or stronger, held for {HUNT_HOLD:.0f}s.", style="dim"),
             Text("Beeps speed up as you get closer (m to mute).", style="dim")]
    body, border = Group(*rows), "magenta"
    if sonar_args is not None:
        dev_, r_, col_ = sonar_args
        border = col_                                       # the panel border runs cold -> hot with the signal
        if CFG["fx"]:
            W, H = size
            if W >= 100 and H >= 12:                        # wide terminal: sonar to the right of the readout
                sonar, sw = build_sonar(now, 2 * min(7, (H - 4) // 2) + 1, col_, dev_, r_)
                grid = Table.grid(padding=(0, 3), expand=True)
                grid.add_column(ratio=1)
                grid.add_column(width=sw, justify="center")
                grid.add_row(Group(*rows), sonar)
                body = grid
            else:                                           # narrow: sonar above, only if there is room for it
                spare = H - 2 - len(rows) - 2
                ry = min(6, (spare - 1) // 2)
                if ry >= 2:
                    sonar, _ = build_sonar(now, 2 * ry + 1, col_, dev_, r_)
                    body = Group(Align.center(sonar), Text(""), *rows)
    return Panel(body, title=title, border_style=border, box=ROUNDED)

# =============================================================================
# STATION STATUS (clock / battery / Bluetooth adapter) & DEVICE INSPECTOR
# =============================================================================
CLOCK_FMT = "%I:%M:%S %p"            # 12-hour clock; use "%H:%M:%S" for 24-hour
BATTERY_TTL = 20.0                   # seconds between battery re-reads (done on a worker thread)
BATTERY = {"t": 0.0, "val": None, "busy": False}
ADAPTER = {"name": "hci1", "product": "", "bus": "", "addr": ""}    # filled in by main() / --adapter
INSPECT = {"mac": None}              # device currently shown in the inspector

def clock_str(ts=None, date: bool = False) -> str:
    dt = datetime.datetime.fromtimestamp(ts) if ts else datetime.datetime.now()
    s = dt.strftime(CLOCK_FMT)
    return f"{dt.strftime('%a %b %d')}  {s}" if date else s

def _battery_probe():
    """(percent, plugged_in) for the machine running the scanner, or None if no battery can be read."""
    try:
        import psutil
        b = psutil.sensors_battery()
        if b is not None:
            return int(round(b.percent)), b.power_plugged
    except Exception:
        pass
    try:
        if sys.platform.startswith("linux"):
            for d in sorted(glob.glob("/sys/class/power_supply/*")):
                try:
                    ps = Path(d)
                    if (ps / "type").read_text().strip() != "Battery":
                        continue
                    if (ps / "scope").is_file() and (ps / "scope").read_text().strip() == "Device":
                        continue                                  # a wireless mouse / headset, not this machine
                    status = (ps / "status").read_text().strip().lower() if (ps / "status").is_file() else ""
                    return int((ps / "capacity").read_text().strip()), status in ("charging", "full", "not charging")
                except Exception:
                    continue
            if shutil.which("termux-battery-status"):             # Android / Termux
                j = json.loads(subprocess.run(["termux-battery-status"], capture_output=True, text=True, timeout=3).stdout)
                return int(j["percentage"]), str(j.get("status", "")).upper() in ("CHARGING", "FULL")
        elif sys.platform == "darwin":
            out = subprocess.run(["pmset", "-g", "batt"], capture_output=True, text=True, timeout=3).stdout
            m = re.search(r"(\d+)%", out)
            if m:
                return int(m.group(1)), "AC Power" in out
        elif sys.platform == "win32":
            import ctypes

            class SYSTEM_POWER_STATUS(ctypes.Structure):
                _fields_ = [("ACLineStatus", ctypes.c_ubyte), ("BatteryFlag", ctypes.c_ubyte),
                            ("BatteryLifePercent", ctypes.c_ubyte), ("SystemStatusFlag", ctypes.c_ubyte),
                            ("BatteryLifeTime", ctypes.c_ulong), ("BatteryFullLifeTime", ctypes.c_ulong)]
            s = SYSTEM_POWER_STATUS()
            if ctypes.windll.kernel32.GetSystemPowerStatus(ctypes.byref(s)) and s.BatteryFlag != 128 and s.BatteryLifePercent != 255:
                return int(s.BatteryLifePercent), s.ACLineStatus == 1
    except Exception:
        pass
    return None

def fmt_eta(seconds: float) -> str:
    m = int(round(seconds / 60.0))
    return f"{m // 60}h {m % 60:02d}m" if m >= 60 else f"{max(m, 1)}m"

def _battery_eta():
    """(seconds, charging) estimate for this machine's battery, or None when it can't be worked out.
    Discharging = time left; charging = time until full. The draw is smoothed over the 20-second probes."""
    try:
        import psutil
        b = psutil.sensors_battery()
        if b is not None and not b.power_plugged and isinstance(b.secsleft, (int, float)) and b.secsleft > 0:
            return float(b.secsleft), False
    except Exception:
        pass
    if sys.platform.startswith("linux"):
        for d in sorted(glob.glob("/sys/class/power_supply/*")):
            ps = Path(d)
            try:
                if (ps / "type").read_text().strip() != "Battery":
                    continue
                if (ps / "scope").is_file() and (ps / "scope").read_text().strip() == "Device":
                    continue                                      # a wireless mouse / headset, not this machine
                status = (ps / "status").read_text().strip().lower()
            except Exception:
                continue
            if status not in ("charging", "discharging"):
                return None                                       # full / not charging / unknown
            def num(name):
                try:
                    return float((ps / name).read_text().strip())
                except Exception:
                    return None
            rate, left, full = num("power_now"), num("energy_now"), num("energy_full")
            if not rate or left is None or not full:              # some batteries only report charge + current
                rate, left, full = num("current_now"), num("charge_now"), num("charge_full")
            if not rate or left is None or not full:
                return None
            rate = abs(rate)
            prev = BATTERY.get("rate")
            smooth = rate if prev is None or BATTERY.get("rate_status") != status else 0.3 * rate + 0.7 * prev
            BATTERY["rate"], BATTERY["rate_status"] = smooth, status
            hours = (left / smooth) if status == "discharging" else ((full - left) / smooth)
            return (hours * 3600.0, status == "charging") if 0 < hours <= 48 else None
    elif sys.platform == "darwin":
        try:
            out = subprocess.run(["pmset", "-g", "batt"], capture_output=True, text=True, timeout=3).stdout
            m = re.search(r"(\d+):(\d+) remaining", out)
            if m:
                return int(m.group(1)) * 3600.0 + int(m.group(2)) * 60.0, False
        except Exception:
            pass
    return None

CPU_TEMP = {"t": 0.0, "val": None, "paths": None}
CPU_TEMP_TTL = 2.0                       # seconds between temperature re-reads (a tiny sysfs read)

def _cpu_temp_paths() -> list:
    """Linux: the CPU / APU temperature files (the Steam Deck's k10temp 'Tctl', Intel coretemp, ARM cpu thermal zones)."""
    paths = []
    if not sys.platform.startswith("linux"):
        return paths
    for hw in sorted(glob.glob("/sys/class/hwmon/hwmon*")):
        try:
            name = Path(hw, "name").read_text().strip()
        except Exception:
            continue
        if name not in ("k10temp", "coretemp", "zenpower", "cpu_thermal", "cpu-thermal", "soc_thermal"):
            continue
        ranked = []
        for f in sorted(glob.glob(f"{hw}/temp*_input")):
            lab = Path(f.replace("_input", "_label"))
            label = lab.read_text().strip() if lab.is_file() else ""
            ranked.append((0 if re.search(r"tctl|tdie|package|cpu", label, re.I) else 1, f))
        if ranked:
            paths.append(sorted(ranked)[0][1])
    if not paths:
        for z in sorted(glob.glob("/sys/class/thermal/thermal_zone*")):
            try:
                if re.search(r"x86_pkg_temp|cpu|soc|acpitz", Path(z, "type").read_text(), re.I):
                    paths.append(f"{z}/temp")
            except Exception:
                continue
    return paths

def cpu_temp_c():
    """Hottest CPU sensor in °C, or None if this machine doesn't expose one. Cached for a couple of seconds."""
    now = time.time()
    if now - CPU_TEMP["t"] < CPU_TEMP_TTL:
        return CPU_TEMP["val"]
    CPU_TEMP["t"] = now
    if CPU_TEMP["paths"] is None:
        CPU_TEMP["paths"] = _cpu_temp_paths()
    best = None
    for p in CPU_TEMP["paths"]:
        try:
            v = int(Path(p).read_text().strip()) / 1000.0
        except Exception:
            continue
        if 1.0 <= v <= 130.0 and (best is None or v > best):
            best = v
    CPU_TEMP["val"] = best
    return best

def cpu_temp_text():
    t = cpu_temp_c()
    if t is None:
        return None
    style = "green" if t < 70 else "yellow" if t < 85 else "bold red"
    return Text(f"🌡 {t:.0f}°C", style=style)

def _battery_refresh():
    try:
        BATTERY["val"] = _battery_probe()
        BATTERY["eta"] = _battery_eta() if BATTERY["val"] is not None else None
    except Exception:
        BATTERY["val"] = None
        BATTERY["eta"] = None
    finally:
        BATTERY["t"] = time.time()
        BATTERY["busy"] = False

def battery_status():
    """Cached battery reading. Refreshes on a worker thread so a slow probe never stalls the dashboard."""
    if not BATTERY["busy"] and time.time() - BATTERY["t"] > BATTERY_TTL:
        BATTERY["busy"] = True
        threading.Thread(target=_battery_refresh, daemon=True).start()
    return BATTERY["val"]

def battery_style(pct: int) -> str:
    return "green" if pct >= 50 else "yellow" if pct >= 20 else "bold red"

def battery_text() -> Text:
    b = battery_status()
    if b is None:
        return Text("🔌 no battery", style="dim")
    pct, plugged = b
    t = Text("🔋 ")
    t.append(f"{pct}%", style=battery_style(pct))
    if plugged:
        t.append(" ⚡", style="yellow")
    eta = BATTERY.get("eta")
    if eta:
        secs, charging = eta
        if charging:
            t.append(f" {fmt_eta(secs)} to full", style="yellow")
        else:
            t.append(f" {fmt_eta(secs)} left", style="bold red" if secs < 1800 else "yellow" if secs < 3600 else "dim")
    return t

def adapter_details(name: str) -> dict:
    """One-time lookup of what the adapter actually is (product / bus / address). Linux + BlueZ only."""
    info = {"product": "", "bus": "", "addr": ""}
    if not sys.platform.startswith("linux"):
        return info
    try:
        dev = (Path("/sys/class/bluetooth") / name / "device").resolve()
        for d in (dev, dev.parent):                  # USB dongles keep their product string one level up
            if (d / "product").is_file():
                maker = (d / "manufacturer").read_text().strip() if (d / "manufacturer").is_file() else ""
                info["product"] = clean(f"{maker} {(d / 'product').read_text().strip()}", 40)
                break
    except Exception:
        pass
    try:
        out = subprocess.run(["hciconfig", name], capture_output=True, text=True, timeout=2).stdout
        m = re.search(r"Bus:\s*(\w+)", out)
        info["bus"] = m.group(1) if m else ""
        m = re.search(r"BD Address:\s*((?:[0-9A-Fa-f]{2}:){5}[0-9A-Fa-f]{2})", out)
        info["addr"] = m.group(1).upper() if m else ""
    except Exception:
        pass
    return info

def adapter_label(full: bool = False) -> str:
    if not sys.platform.startswith("linux"):
        return "system default"                      # bleak only honours an adapter choice on Linux / BlueZ
    a = ADAPTER
    bits = [a["name"], a["product"]] + ([a["bus"], a["addr"]] if full else [])
    return " · ".join(b for b in bits if b)

def station_line() -> Text:
    """Clock, battery of the machine running the scanner, and the Bluetooth adapter in use (HUD row 3)."""
    t = Text(no_wrap=True, overflow="ellipsis")
    t.append("🕒 ", style="dim")
    t.append(clock_str(), style="bold bright_white")
    t.append("  │  ", style="dim")
    t.append_text(battery_text())
    ct = cpu_temp_text()
    if ct is not None:
        t.append("  │  ", style="dim")
        t.append_text(ct)
    t.append("  │  ", style="dim")
    t.append_text(heartbeat_text(time.time()))
    t.append("  │  ", style="dim")
    t.append("📶 adapter ", style="dim")
    t.append(adapter_label(), style="cyan")
    return t

def kv_table() -> Table:
    g = Table.grid(padding=(0, 2), expand=True)
    g.add_column(style="bold yellow", no_wrap=True)
    g.add_column(ratio=1, overflow="fold")
    return g

def build_station_panel(now: float) -> Panel:
    g = kv_table()
    g.add_row("Time", Text(clock_str(now, date=True), style="bold bright_white"))
    b = battery_status()
    if b is None:
        g.add_row("Battery", Text("none detected", style="dim"))
    else:
        pct, plugged = b
        col = battery_style(pct)
        row = mini_bar(pct / 100, 16, col)
        row.append(f" {pct}%", style=col)
        if plugged:
            row.append("  ⚡ plugged in", style="yellow")
        eta = BATTERY.get("eta")
        if eta:
            row.append(f"  {fmt_eta(eta[0])} to full" if eta[1] else f"  {fmt_eta(eta[0])} left", style="dim")
        g.add_row("Battery", row)
    ct = cpu_temp_text()
    if ct is not None:
        g.add_row("CPU temp", ct)
    g.add_row("BT adapter", Text(adapter_label(True)))
    return Panel(g, title="[bold]🖥 This station[/]", title_align="left", border_style="cyan", box=ROUNDED, padding=(0, 1))

def inspect_identity_panel(dev: Dev, now: float) -> Panel:
    i = dev.ident
    live = now - dev.last <= ACTIVE_WINDOW
    g = kv_table()
    g.add_row("Name", Text(display_name(dev), style="bold"))
    g.add_row("MAC", Text(f"{dev.mac}  ({i.addr_type})"))
    g.add_row("Status", Text("● LIVE" if live else f"○ last heard {fmt_dur(now - dev.last, True)} ago",
                             style="bright_green" if live else "yellow"))
    g.add_row("Category", Text(i.category, style=CATEGORY_COLORS.get(i.category, "cyan")))
    if i.label:
        g.add_row("Identified as", Text(i.label))
    if i.vendor:
        g.add_row("Vendor", Text(i.vendor, style="cyan"))
    if i.tier:
        g.add_row("Tier", Text(f"{i.tier.upper()} · confidence {i.confidence}",
                               style="bold red" if i.tier == "alert" else "bold yellow" if i.tier == "possible" else "green"))
    if i.known:
        g.add_row("Known as", Text(i.known, style="bold green"))
    if dev.name:
        g.add_row("Adv. name", Text(dev.name))
    if dev.mfg_text:
        g.add_row("Manufacturer", Text(dev.mfg_text))
    if dev.classic:
        g.add_row("Classic BT", Text(f"BR/EDR device · Class 0x{dev.cod:06X} · {cod_info(dev.cod)[1]}", style="cyan"))
    if dev.sensor:
        sn = dev.sensor
        g.add_row("Sensor", Text(f"{sn['fmt']} · decoded {fmt_dur(now - sn['t'], True)} ago", style="bold green"))
        for lab, val in sn["vals"]:
            g.add_row(f"  {lab}", Text(val, style="bright_white"))
    if dev.uuids:
        u = sorted(dev.uuids)
        g.add_row("Services", Text(", ".join(u[:10]) + (f" … +{len(u) - 10} more" if len(u) > 10 else "")))
    if i.reasons:
        g.add_row("Why", Text("; ".join(clean(r, 60) for r in i.reasons[:4]), style="dim"))
    gh = GHOSTS.get(dev.ghost_id)
    if gh and len(gh.macs) > 1:
        others = [m for m in gh.macs if m != dev.mac]
        g.add_row("Linked MACs", Text(f"{len(gh.macs)} addresses (probable rotations): " + ", ".join(others[-3:])
                                      + (" …" if len(others) > 3 else ""), style="dim"))
    border = "red" if i.tier == "alert" else "yellow" if i.tier == "possible" else CATEGORY_COLORS.get(i.category, "cyan")
    return Panel(g, title="[bold]🔍 Device Inspector (c close · Enter pick another · y connect)[/]", title_align="left",
                 border_style=border, box=ROUNDED, padding=(0, 1))

def inspect_signal_panel(dev: Dev, now: float, width: int) -> Panel:
    sym, tcol = trend(dev, now)
    d_ft = est_distance_ft(dev.ema, dev.tx)
    g = kv_table()
    sig = Text(f"{dev.rssi} dBm now · {dev.ema:.0f} smoothed  ")
    sig.append_text(sig_bar(dev.ema))
    sig.append(f" {sym}", style=tcol)
    g.add_row("Signal", sig)
    g.add_row("Distance", Text(">300 ft" if d_ft > 300 else f"~{d_ft:.1f} ft (estimate)"))
    g.add_row("Tx power", Text("not advertised" if dev.tx is None else f"{dev.tx} dBm"))
    g.add_row("Packets", Text(f"{dev.packets}  (~{dev.packets / max(1.0, now - dev.first):.1f}/s)"))
    g.add_row("First seen", Text(f"{clock_str(dev.first)}  ({fmt_dur(now - dev.first, True)} ago)"))
    g.add_row("Last heard", Text(f"{clock_str(dev.last)}  ({fmt_dur(now - dev.last, True)} ago)"))
    tail = TAILS.get(dev.mac)
    if tail and tail.tier:
        label, style = FOLLOW_STYLE[tail.tier]
        g.add_row("Follower", Text(f"{label} · near you {fmt_dur(tail.near_s, True)}", style=style))
    g.add_row("Last 20s", sparkline(dev, now, 20.0, max(10, min(40, width - 16))))
    return Panel(g, title="[bold]📶 Signal & activity[/]", title_align="left", border_style="cyan", box=ROUNDED, padding=(0, 1))

# =============================================================================
# CONNECT PROBE (inspector, key y)
# Actively connects to ONE device and reads what it will freely tell you over GATT: the Device Information
# service (manufacturer / model / firmware / serial), battery level, appearance, PnP ID, and the list of services
# it offers. Read-only: nothing is ever written to the device and no pairing is requested. The device (and its
# owner) can see that a connection was made, so only probe devices you own or have permission to probe.
# =============================================================================
PROBE_TIMEOUT = 15.0        # seconds allowed for the connection itself
PROBE_READ_TIMEOUT = 5.0    # seconds allowed per characteristic read
PROBE_OTHER_MAX = 12        # max unrecognised readable characteristics to read and show
SCAN = {"scanner": None}    # the live BleakScanner, set by amain, so a probe can pause it
PROBE_SETTLE = 0.4          # seconds to let the adapter settle after stopping / before restarting the scan
PROBES: dict = {}           # mac -> {"state", "t", "info", "services", "other", "protected", "error"}

GATT_SERVICES = {
    0x1800: "Generic Access", 0x1801: "Generic Attribute", 0x1802: "Immediate Alert", 0x1803: "Link Loss",
    0x1804: "Tx Power", 0x1805: "Current Time", 0x180A: "Device Information", 0x180D: "Heart Rate",
    0x180F: "Battery", 0x1810: "Blood Pressure", 0x1812: "HID (keyboard/mouse/remote)", 0x1816: "Cycling Speed",
    0x1818: "Cycling Power", 0x1819: "Location & Navigation", 0x181A: "Environmental Sensing", 0x181D: "Weight Scale",
    0x181F: "Continuous Glucose", 0x183B: "Binary Sensor", 0x184E: "Audio Stream Control", 0x1850: "Published Audio",
    0xFE2C: "Google Fast Pair", 0xFD6F: "Exposure Notification", 0xFEAA: "Eddystone", 0xFEF3: "Google",
    0xFD44: "Apple (Find My / Nearby)", 0xFE9F: "Google",
}
GATT_INFO = {
    0x2A00: "Device name", 0x2A01: "Appearance", 0x2A19: "Battery level", 0x2A23: "System ID",
    0x2A24: "Model number", 0x2A25: "Serial number", 0x2A26: "Firmware revision", 0x2A27: "Hardware revision",
    0x2A28: "Software revision", 0x2A29: "Manufacturer", 0x2A50: "PnP ID",
}
APPEARANCE = {0: "Unknown", 1: "Phone", 2: "Computer", 3: "Watch", 4: "Clock", 5: "Display", 6: "Remote control",
              7: "Eyeglasses", 8: "Tag", 9: "Keyring", 10: "Media player", 11: "Barcode scanner", 12: "Thermometer",
              13: "Heart rate sensor", 14: "Blood pressure", 15: "HID device", 16: "Glucose meter",
              17: "Running/walking sensor", 18: "Cycling sensor"}
_BASE_UUID_TAIL = "-0000-1000-8000-00805f9b34fb"

def sig_uuid(u: str):
    """16-bit value of a Bluetooth-SIG base UUID, else None (vendor-specific UUID)."""
    u = str(u).lower()
    if u.startswith("0000") and u.endswith(_BASE_UUID_TAIL):
        try:
            return int(u[4:8], 16)
        except ValueError:
            return None
    return None

def service_label(u: str) -> str:
    s = sig_uuid(u)
    if s is None:
        return f"vendor {str(u)[:8]}…"
    return GATT_SERVICES.get(s, f"0x{s:04X}")

def _decode_value(data: bytes) -> str:
    if not data:
        return "(empty)"
    try:
        txt = bytes(data).split(b"\x00")[0].decode("utf-8")
        if txt and txt.isprintable():
            return clean(txt, 60)
    except UnicodeDecodeError:
        pass
    h = bytes(data[:16]).hex()
    return "0x" + h + ("…" if len(data) > 16 else "")

def decode_gatt(short: int, data: bytes) -> str:
    if short == 0x2A19 and data:
        return f"{data[0]}%"
    if short == 0x2A01 and len(data) >= 2:
        val = int.from_bytes(data[:2], "little")
        return f"{APPEARANCE.get(val >> 6, 'category ' + str(val >> 6))} (0x{val:04X})"
    if short == 0x2A50 and len(data) >= 7:
        return f"vendor 0x{int.from_bytes(data[1:3], 'little'):04X} · product 0x{int.from_bytes(data[3:5], 'little'):04X}" \
               f" · version 0x{int.from_bytes(data[5:7], 'little'):04X}"
    if short == 0x2A23:
        return "0x" + bytes(data).hex()
    return _decode_value(data)

def probe_active() -> bool:
    return any(p["state"] in ("connecting", "reading") for p in PROBES.values())

async def probe_device(mac: str):
    st = PROBES[mac]
    client = None
    sc = SCAN["scanner"]
    paused = cancelled = cpaused = False
    try:
        cpaused = await classic_pause()
        if sc is not None and CFG["scanning"]:
            # BlueZ often refuses to connect while it is scanning, so pause the scan for the connection.
            try:
                await sc.stop()
                CFG["scanning"] = False
                paused = True
                log_event("Scanning paused for connect probe")
                await asyncio.sleep(PROBE_SETTLE)
            except Exception as e:
                st["note"] = f"couldn't pause scan: {clean(str(e), 60)}"
        dev = DEVICES.get(mac)
        target = (dev.ble if dev is not None and dev.ble is not None else mac)
        kw = {"timeout": PROBE_TIMEOUT}
        if sys.platform.startswith("linux"):
            kw["adapter"] = ADAPTER["name"]
        try:
            client = bleak.BleakClient(target, **kw)
        except TypeError:
            kw.pop("adapter", None)
            client = bleak.BleakClient(target, **kw)
        t0 = time.time()
        await asyncio.wait_for(client.connect(), PROBE_TIMEOUT + 5)
        st["state"] = "reading"
        st["connect_s"] = time.time() - t0
        try:
            st["mtu"] = client.mtu_size
        except Exception:
            pass
        others = 0
        for svc in client.services:
            chars = list(svc.characteristics)
            st["services"].append((service_label(svc.uuid), len(chars)))
            for ch in chars:
                if "read" not in ch.properties:
                    continue
                s = sig_uuid(ch.uuid)
                known = s in GATT_INFO
                if not known:
                    if others >= PROBE_OTHER_MAX or (s is not None and s in (0x2A04, 0x2A05, 0x2A06)):
                        continue
                    others += 1
                try:
                    data = await asyncio.wait_for(client.read_gatt_char(ch), PROBE_READ_TIMEOUT)
                except asyncio.TimeoutError:
                    continue
                except Exception:
                    st["protected"] += 1          # needs pairing / encryption: we do not pair
                    continue
                if known:
                    st["info"].append((GATT_INFO[s], decode_gatt(s, bytes(data))))
                else:
                    name = (f"{service_label(svc.uuid)} · " if s is None else "") + (f"0x{s:04X}" if s is not None else str(ch.uuid)[:8])
                    st["other"].append((name, _decode_value(bytes(data))))
        st["state"] = "done"
    except asyncio.CancelledError:
        cancelled = True
        raise
    except asyncio.TimeoutError:
        st["state"], st["error"] = "failed", "Timed out. The device may be out of range, busy, or not connectable."
    except Exception as e:
        st["state"], st["error"] = "failed", clean(str(e) or e.__class__.__name__, 120)
    finally:
        if client is not None:
            try:
                await asyncio.wait_for(client.disconnect(), 5)
            except Exception:
                pass
        st["done_t"] = time.time()
        if cpaused and not cancelled:
            await classic_resume()
        if paused and not cancelled and sc is not None:
            try:
                await asyncio.sleep(PROBE_SETTLE)
                await sc.start()
                CFG["scanning"] = True
                log_event("Scanning resumed after connect probe")
            except Exception as e:
                st["note"] = f"scan did not restart ({clean(str(e), 60)}); press s to resume"

def start_probe() -> str:
    """Key y: connect to the device open in the inspector and read its GATT info."""
    mac = INSPECT["mac"]
    if not CFG["show_inspect"] or not mac:
        return "Open the inspector first (c / Enter), then press y to connect to that device."
    dev = DEVICES.get(mac)
    if dev is None:
        return f"{mac} isn't being heard right now, so it can't be connected to."
    cur = PROBES.get(mac)
    if probe_active():
        return "Already connecting…"
    PROBES[mac] = {"state": "connecting", "t": time.time(), "info": [], "services": [], "other": [],
                   "protected": 0, "error": ""}
    asyncio.create_task(probe_device(mac))
    return f"Connecting to {mac}: scan paused meanwhile, read-only, no pairing…"

def inspect_probe_panel(dev: Dev, now: float):
    st = PROBES.get(dev.mac)
    if st is None:
        return None
    g = kv_table()
    state = st["state"]
    if state in ("connecting", "reading"):
        dots = "." * (1 + int(now * 2) % 3)
        g.add_row("Status", Text(("Connecting" if state == "connecting" else "Reading services") + dots
                                 + f" ({now - st['t']:.0f}s)", style="bold yellow"))
    elif state == "failed":
        g.add_row("Status", Text("✖ Connection failed", style="bold red"))
        g.add_row("Reason", Text(st["error"], style="red"))
        if "le-connection-abort" in st["error"].lower() or "InProgress" in st["error"]:
            g.add_row("Tip", Text("The adapter was busy. Press y to retry.", style="dim"))
    else:
        took = f"{st.get('connect_s', 0):.1f}s" + (f" · MTU {st['mtu']}" if st.get("mtu") else "")
        g.add_row("Status", Text(f"✔ Connected and read ({took}), then disconnected", style="bold green"))
    if state in ("connecting", "reading"):
        g.add_row("Scan", Text("paused while connecting; resumes automatically", style="dim"))
    if st.get("note"):
        g.add_row("Note", Text(st["note"], style="yellow"))
    for label, val in st["info"]:
        g.add_row(label, Text(val, style="bright_white"))
    if st["services"]:
        names = [f"{n} ({c})" for n, c in st["services"]]
        g.add_row("Services", Text(", ".join(names[:12]) + (f" … +{len(names) - 12} more" if len(names) > 12 else "")))
    for label, val in st["other"][:8]:
        g.add_row(label, Text(val, style="dim"))
    if st["protected"]:
        g.add_row("Protected", Text(f"{st['protected']} characteristic(s) need pairing and were skipped", style="dim"))
    if state == "done" and not st["info"] and not st["other"]:
        g.add_row("Result", Text("Connected, but the device exposes no freely readable information.", style="dim"))
    return Panel(g, title="[bold]🔗 Connection probe (y retry)[/]", title_align="left",
                 border_style="green" if state == "done" else "red" if state == "failed" else "yellow",
                 box=ROUNDED, padding=(0, 1))

def build_inspect_panel(size):
    W, H = size
    now = time.time()
    mac = INSPECT["mac"]
    dev = DEVICES.get(mac) if mac else None
    station = build_station_panel(now)
    if dev is None:
        msg = ("No device selected. Press Enter to pick one." if not mac else
               f"{mac} hasn't been heard yet (or it is ignored). Waiting for it to advertise… Enter picks another device.")
        body = Layout()
        body.split_column(Layout(Panel(Text(msg), title="[bold]🔍 Device Inspector (c close · Enter pick another)[/]",
                                       title_align="left", border_style="cyan", box=ROUNDED), ratio=1),
                          Layout(station, size=6))
        return body
    body = Layout()
    probe = inspect_probe_panel(dev, now)
    if W >= 100:
        right = Layout(ratio=2)
        right.split_column(Layout(inspect_signal_panel(dev, now, int(W * 2 / 5)), ratio=1), Layout(station, size=6))
        if probe is not None:
            left = Layout(ratio=3)
            left.split_column(Layout(inspect_identity_panel(dev, now), ratio=3), Layout(probe, ratio=2))
        else:
            left = Layout(inspect_identity_panel(dev, now), ratio=3)
        body.split_row(left, right)
    else:
        parts = [Layout(inspect_identity_panel(dev, now), ratio=3)]
        if probe is not None:
            parts.append(Layout(probe, ratio=3))
        parts += [Layout(inspect_signal_panel(dev, now, W), ratio=3), Layout(station, size=6)]
        body.split_column(*parts)
    return body

HUD_HEIGHT = 5                                  # three text rows + panel border (+1 for the game strip, +1 while a mission runs)

def build_hud(width: int, now: float, strip=None, mission=None) -> Panel:
    """Status HUD shown above every view: app/toggle row, then scan stats, then a station row (clock / battery / BT adapter)."""
    top = Text(no_wrap=True, overflow="ellipsis")
    top.append("🛡 SIGNAL OPS ", style="bold cyan")
    top.append(f"v{VERSION}", style="dim cyan")
    if GAME["on"] and STATE.get("name"):
        top.append("  |  ", style="dim")
        if SUPPORT["on"]:
            top.append_text(sparkle_text(STATE["name"], now))
        else:
            top.append(STATE["name"], style="bold bright_white")
    top.append("  |  Scan: ", style="dim")
    top.append("ON" if CFG["scanning"] else "OFF", style="green" if CFG["scanning"] else "red")
    top.append("  Dedup: ", style="dim")
    top.append("ON" if CFG["dedup"] else "OFF", style="green" if CFG["dedup"] else "red")
    if CLASSIC["on"]:
        top.append("  Classic: ", style="dim")
        top.append("ON", style="green")
    top.append("  Mute: ", style="dim")
    top.append("MUTED" if MUTED else "ACTIVE", style="red" if MUTED else "green")
    if CFG["auto_tactical"]:
        top.append("  AutoTac: ", style="dim")
        top.append("ON", style="green")
    top.append("  Notify: ", style="dim")
    nlabel = NOTIFY_SOUNDS[NOTIFY["idx"]][1]
    top.append(nlabel, style="red" if NOTIFY_SOUNDS[NOTIFY["idx"]][0] is None else "green")
    thr = CFG["min_rssi"]
    top.append("  Sig: ", style="dim")
    top.append("ALL" if thr is None else f"≥{thr} dBm", style="green" if thr is None else "yellow")
    hid = hidden_count(now)
    if hid:
        top.append(f" (+{hid} hidden)", style="dim")
    n_follow = follow_alerts()
    if n_follow:
        top.append(f"  ⚠ {n_follow} possible follower{'s' if n_follow != 1 else ''} (f)", style="bold red")
    if hunting():
        hd = DEVICES.get(HUNT["mac"])
        top.append("  🔎 Hunt: " + (hunt_temp(hd.ema)[0] if hd and now - hd.last <= 5 else "searching"), style="bold magenta")

    live = "bright_white" if CFG["scanning"] else "dim"
    flagged_devs = [d for d in DEVICES.values() if now - d.last <= CFG["stale"] and d.ident.tier in ("alert", "possible")]
    flagged = len(flagged_devs)
    hud_level = "alert" if (n_follow or any(d.ident.tier == "alert" for d in flagged_devs)) else ("possible" if flagged_devs else "")
    stats = Text(no_wrap=True, overflow="ellipsis")
    gh = game_hud_text()
    if gh is not None:
        stats.append_text(gh)
        stats.append(" │ ", style="dim")
    stats.append(f"⏱ scanned {fmt_dur(SESSION['scan_seconds'])}", style=live)
    stats.append(" │ ", style="dim")
    in_range = sum(1 for d in DEVICES.values() if d.counted and now - d.last <= CFG["stale"])   # same rule as the game's crowd counter
    stats.append(f"📡 {in_range} in range", style="bold cyan")
    stats.append(f" · {len(SEEN)} seen", style="cyan")
    stats.append(" │ ", style="dim")
    stats.append(f"🎯 {flagged} tactical", style=throb_text("red", hud_level, now) if flagged else "dim")
    stats.append(" │ ", style="dim")
    stats.append(f"👁 {current_view()[1]}", style="bright_white")
    rows = [top, stats, station_line()] + ([strip] if strip is not None else []) + ([mission] if mission is not None else [])
    return Panel(Group(*rows), border_style=throb_border("cyan", hud_level, now), box=ROUNDED, padding=(0, 1))

def build_dashboard(size):
    """HUD on top of every view, then the active view, then the status line."""
    now = time.time()
    W, H = size
    fx = fx_visible(now)
    if fx:
        screen = build_fx_screen(fx, size, now)
        if screen is not None:
            return crt_wrap(screen, now)
    strip = game_strip_text(now)
    mstrip = mission_strip_text(now)
    hud_h = HUD_HEIGHT + (1 if strip is not None else 0) + (1 if mstrip is not None else 0)
    root = Layout()
    root.split_column(
        Layout(build_hud(W, now, strip, mstrip), size=hud_h),
        Layout(build_view((W, max(5, H - hud_h - 1))), ratio=1),
        Layout(decrypt_status_text(now), size=1),
    )
    return crt_wrap(root, now)

def build_view(size):
    """The active screen's body. (size is the space left for it below the HUD.)"""
    W, H = size
    now = time.time()
    spin = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"[int(now * 8) % 10]

    if CFG["show_help"]:
        return build_help_panel(size)
    if CFG["show_tutorial"]:
        return build_tutorial_panel(size)
    if CFG["show_missions"]:
        return build_missions_panel(size)
    if CFG["show_profile"]:
        return build_profile_panel(size)
    if CFG["show_follow"]:
        return build_follow_panel(size)
    if CFG["show_hunt"]:
        return build_hunt_panel(size)
    if CFG["show_inspect"]:
        return build_inspect_panel(size)
    kind = current_view()[0]
    if kind == "compact":
        return build_compact_view(size, now)
    elif kind == "tactical":
        return build_tactical_view(size, now)
    elif kind == "security":
        return build_security_view(size, now)
    elif kind in EXTRA_VIEWS:
        return EXTRA_VIEWS[kind](size, now)
    elif kind.startswith("cat:"):
        return build_category_view(size, now, kind[4:])

    groups, tactical, known = group_devices(now)
    subs = CFG["subtitles"]

    cats = [c for c in CATEGORIES if not (CFG["civilian_filter"] and c[0] in CIVILIAN)]
    cols = 3 if W >= 150 else 2 if W >= 100 else 1
    n_cells = len(cats) + 1
    n_rows = math.ceil(n_cells / cols)
    cells = [device_panel(f"[bold {color}]{icon} {title} ({len(groups.get(key, []))})[/]", color, groups.get(key, []), 4, now, subs, spin)
             for key, icon, title, color in cats]

    st_table = Table.grid(expand=True)
    st_table.add_row(Text(f"Seen: {len(SEEN)} | Packets/s: {STATS['pps']:.0f} | Shortcuts: [s] Scan, [d] Dedup, [r] Rename, [c] Inspect, [i] Ignore, [f] Followers, [g] Hunt, [m] Mute, [n] Notify sound, [v] Next view, [w] Pick view, [ / ] Signal filter, [o] CRT, [p] Profile, [y] Missions, [b] Guide, [u] Auto-tactical, [$] Support the dev, [h] Help, [q] Quit", style="dim"))
    cells.append(Panel(st_table, title="[bold]📊 SESSION & SHORTCUTS[/]", border_style="grey50", box=ROUNDED))

    body = Layout()
    rows = [Layout(name=f"r{i}") for i in range(n_rows)]
    body.split_column(*rows)
    for i, row in enumerate(rows):
        row.split_row(*[Layout(c) for c in cells[i * cols:(i + 1) * cols]])
    return body

# =============================================================================
# BOOT SEQUENCE
# A short fake startup shown once the Bluetooth adapter has really started: adapter handshake, database loading, a
# loading bar and an ACCESS GRANTED banner, which is also where the 'intro' sound plays. Any key skips it.
# The values on screen are real (adapter, database sizes, your profile); only the pacing is staged.
# Tune or turn it off with the "boot" block of lookout_game.json (enabled, speed, banner, play_intro, lines),
# or skip it for one run with --no-boot (--boot / --no-boot-sound and the "boot" / "boot_sound" settings still work). --no-fx and non-interactive terminals skip it too.
# =============================================================================
BOOT = {"pending": False, "cfg_status": "", "active": False}
GAME_DEFAULT_BOOT = {"enabled": True, "speed": 1.0, "banner": "ACCESS GRANTED", "play_intro": True, "lines": []}

def boot_wanted(no_boot: bool) -> bool:
    if no_boot or not (HAVE_RICH and HAVE_TTY and sys.stdin.isatty() and sys.stdout.isatty()):
        return False
    if not CFG["fx"] or not CFG.get("boot", True):          # --no-fx, or "boot": false in lookout_settings.json (--boot forces it on)
        return False
    return bool((GCFG.get("boot") or GAME_DEFAULT_BOOT).get("enabled", True))

def _boot_line(tag: str, tag_style: str, text: str, detail: str = "") -> Text:
    t = Text(no_wrap=True, overflow="ellipsis")
    t.append(f"  [{tag:^6}] ", style=tag_style)
    t.append(text.ljust(30), style="bright_white")
    if detail:
        t.append(" " + detail, style="cyan")
    return t

def boot_banner_rows(banner: str, W: int, H: int) -> list:
    """Big block letters for the banner (falls back to plain text if the font can't spell it)."""
    return fx_big(banner, max(10, W - 12), max(5, H - 10)) or [banner]

def boot_sequence(console, cfg_status: str = "") -> None:
    """Blocking (run it in a thread). Takes over the terminal for a few seconds, then hands it back."""
    b = GCFG.get("boot") or GAME_DEFAULT_BOOT
    speed = max(0.25, float(b.get("speed", 1.0)))
    fd = sys.stdin.fileno()
    saved = termios.tcgetattr(fd)
    skipped = {"v": False}
    lines: list = []
    st = {"bar": None, "label": "", "banner": None, "frac": 1.0, "phase": 0, "sub": []}

    def key_hit() -> bool:
        try:
            if select.select([fd], [], [], 0)[0]:
                os.read(fd, 64)
                return True
        except Exception:
            pass
        return False

    def wait(sec: float):
        end = time.time() + sec / speed
        while not skipped["v"]:
            left = end - time.time()
            if left <= 0:
                return
            if key_hit():
                skipped["v"] = True
                return
            time.sleep(min(0.02, left))

    def frame():
        W, H = console.size
        if st["banner"] is not None:
            rows = boot_banner_rows(st["banner"], W, H)
            out = []
            phase = st["phase"]
            for r in rows:
                if not r.strip():
                    out.append(Text(" " * len(r)))
                    continue
                shown = r[: int(len(r) * st["frac"])].ljust(len(r))        # left-to-right wipe-in
                out.append(Text(shown, style="bold bright_green" if phase % 2 == 0 else "bold green", no_wrap=True))
            out.append(Text(""))
            for txt, style in st["sub"]:
                out.append(Text(txt, style=style, no_wrap=True, overflow="ellipsis"))
            return Panel(Align.center(Group(*[Align.center(x) for x in out]), vertical="middle"), height=H, box=DOUBLE,
                         border_style="bold bright_green" if phase % 2 == 0 else "green")
        body = lines[-max(3, H - 8):]
        if st["bar"] is not None:
            width = max(10, min(46, W - 34))
            bar = Text("\n  LOADING  ", style="bold green")
            bar.append_text(mini_bar(st["bar"], width, "green"))
            bar.append(f" {int(st['bar'] * 100):3d}%  ", style="bold bright_white")
            bar.append(st["label"], style="dim")
            body = body + [bar]
        return Panel(Group(*body), title="[bold green]SIGNAL OPS // BOOT[/]", title_align="left",
                     subtitle=Text("any key: skip", style="dim"), border_style="green", box=ROUNDED, height=H)

    def section(title: str):
        if skipped["v"]:
            return
        if lines:
            lines.append(Text(""))
        lines.append(Text(f"  ▌{title}", style="bold bright_cyan"))
        live.update(frame(), refresh=True)
        wait(0.12)

    def step(text: str, detail: str = "", ok: str = "OK", jitter=(0.06, 0.17)):
        if skipped["v"]:
            return
        lines.append(_boot_line("..", "dim", text, detail))
        live.update(frame(), refresh=True)
        wait(random.uniform(*jitter))
        lines[-1] = _boot_line(ok, "bold green", text, detail)
        live.update(frame(), refresh=True)

    def play_boot_start():
        """boot.(mp3|wav|ogg|flac): plays the moment the sequence starts. No file = silence (it never falls back to notify)."""
        if b.get("play_intro", True) and CFG.get("boot_sound", True) and find_sound("boot"):
            play_notification_sound("boot")

    def play_intro():
        if b.get("play_intro", True) and CFG.get("boot_sound", True):      # --no-boot-sound / "boot_sound": false silences it
            play_notification_sound("intro", intro=True)

    try:
        tty.setcbreak(fd)
        BOOT["active"] = True
        play_boot_start()
        with Live(console=console, screen=True, auto_refresh=False, transient=True) as live:
            lines.append(Text(f"  SIGNAL OPS v{VERSION}  ·  tactical BLE awareness suite", style="bold bright_white"))
            lines.append(Text("  passive listening only: nothing is paired, connected or transmitted", style="dim"))
            section("BLUETOOTH ADAPTER HANDSHAKE")
            step("HCI reset", ADAPTER["name"])
            step("Open controller", " · ".join(x for x in (ADAPTER.get("bus", ""), ADAPTER.get("product", "")) if x) or "generic HCI controller")
            step("Read BD address", ADAPTER.get("addr") or "not exposed by the OS")
            step("Scan mode", "ACTIVE · listen only, no pairing, no connections")
            step("Handshake", "adapter online", ok="LINK", jitter=(0.2, 0.35))
            section("LOADING DATABASES")
            step("IEEE OUI registry", f"{len(REG.oui):,} prefixes" if REG.oui else "built-in set (run --update-db for the full list)")
            step("Bluetooth SIG company IDs", f"{len(REG.company):,} · {REG.sig_source}")
            step("Detection config", clean(cfg_status, 48) or "defaults")
            step("Tactical signatures", f"{len(CFG_OUI)} OUI rules · {len(CATEGORIES)} panels")
            section("OPERATOR")
            if GAME["on"]:
                lvl = game_level()
                step("Profile", f"{STATE['name']} · level {lvl}" + (f" · {game_rank(lvl)}" if game_rank(lvl) else ""))
                d = game_day()
                step("Daily quests", f"{sum(1 for q in d['quests'] if q in d['done'])}/{len([q for q in d['quests'] if q in GAME['qmap']])} complete")
                step("Mission board", f"{len(GCFG.get('missions', []))} missions · press {MISSION_KEY}")
                step("Intel Coins", f"{coin_state()['bal']:,} {ci()}")
            else:
                step("Game layer", "off (--no-game)", ok="SKIP")
            for extra in b.get("lines", []):
                step(extra)
            if not skipped["v"]:
                stages = ["core", "identification", "tactical rules", "ghost linker", "radar", "game layer", "interface"]
                n = 40
                for i in range(n + 1):
                    st["bar"] = i / n
                    st["label"] = stages[min(len(stages) - 1, int(st["bar"] * len(stages)))]
                    live.update(frame(), refresh=True)
                    wait(0.04)
                    if skipped["v"]:
                        break
            if not skipped["v"]:
                st["banner"] = b.get("banner", "ACCESS GRANTED")
                lvl = game_level() if GAME["on"] else 0
                name = STATE.get("name", "") if GAME["on"] else ""
                st["sub"] = ([(f"Welcome back, {name}" + (f"  ·  level {lvl}" if lvl else ""), "bold bright_white")] if name else []) + \
                            [("adapter online  ·  scanning", "green")]
                play_intro()
                st["frac"] = 0.0
                for k in range(9):                                          # wipe the banner in
                    st["frac"], st["phase"] = k / 8, k
                    live.update(frame(), refresh=True)
                    wait(0.05)
                    if skipped["v"]:
                        break
                for k in range(9, 9 + 14):                                  # hold, with a slow flicker
                    st["frac"], st["phase"] = 1.0, k // 2
                    live.update(frame(), refresh=True)
                    wait(0.12)
                    if skipped["v"]:
                        break
            if skipped["v"] and not INTRO["started"]:
                play_intro()                                                # skipped early: the intro still plays
    finally:
        BOOT["active"] = False
        termios.tcsetattr(fd, termios.TCSADRAIN, saved)
        termios.tcflush(fd, termios.TCIFLUSH)

# =============================================================================
# SESSION COMPLETE SCREEN
# Shown when you quit (q / Esc / Ctrl+C), after the scanner stops: a recap of the session (time online, devices seen,
# packets, XP earned, level, streak, Intel Coins, quests / bounties / missions done) and the milestones you hit, with the
# 'shutdown' sound. The first key press finishes the reveal, the next one closes it (it closes by itself after a few seconds).
# --no-outro skips it, --test-outro previews it right away, --no-fx and non-interactive terminals skip it too.
# =============================================================================
OUTRO_HOLD = 60.0                # seconds the finished screen stays up if you don't press a key
OUTRO_MILESTONE_KINDS = ("level", "achievement", "title", "streak", "bounty", "mission")
SHUTDOWN = {"played": False}

def outro_wanted(no_outro: bool) -> bool:
    if no_outro or not (HAVE_RICH and HAVE_TTY and sys.stdin.isatty() and sys.stdout.isatty()):
        return False
    return bool(CFG["fx"])

def outro_stats() -> dict:
    """Everything the session-complete screen shows, as plain data."""
    now = time.time()
    start = SESSION.get("start") or now
    live = [d for d in DEVICES.values() if d.counted]
    s = {"wall": max(0.0, now - start), "scan": SESSION["scan_seconds"], "seen": len(SEEN), "packets": STATS["packets"],
         "cats": len({d.ident.category for d in live if d.ident.category}),
         "alerts": sum(1 for d in live if d.ident.tier == "alert"),
         "possibles": sum(1 for d in live if d.ident.tier == "possible"), "game": None, "milestones": []}
    if not GAME["on"]:
        return s
    log = GAME["session_log"]
    def n(kind: str, needle: str = "") -> int:
        return sum(1 for _, k, x in log if k == kind and needle in x)
    lvl, into, need = game_progress()
    s["game"] = {"name": STATE.get("name", ""), "level": lvl, "start_level": GAME["session_start_level"], "rank": game_rank(lvl),
                 "into": into, "need": need, "xp": GAME["session_xp"], "total_xp": STATE["xp"], "coins": GAME["session_coins"],
                 "balance": coin_state()["bal"], "streak": STATE["streak"], "best_streak": STATE["best_streak"],
                 "quests": n("quest"), "bounties": n("bounty"), "achievements": n("achievement"),
                 "missions": n("mission", "MISSION COMPLETE"), "missions_failed": n("mission", "MISSION FAILED")}
    s["milestones"] = [x for _, k, x in log if k in OUTRO_MILESTONE_KINDS and (k != "mission" or "MISSION COMPLETE" in x)]
    return s

def _outro_rows(s: dict, ms_limit: int = 6) -> list:
    """The stat block as (kind, label, value[, extra]) rows: head / line / bar / ms / blank."""
    mins = lambda sec: fmt_dur(sec) if sec >= 1 else "0s"
    rows = [("head", "THIS SESSION", ""),
            ("line", "Time online", mins(s["wall"])), ("line", "Scanning time", mins(s["scan"])),
            ("line", "Devices seen", f"{s['seen']:,}"), ("line", "Packets received", f"{s['packets']:,}"),
            ("line", "Categories found", str(s["cats"]))]
    if s["alerts"] or s["possibles"]:
        rows.append(("line", "Flagged", f"{s['alerts']} ALERT · {s['possibles']} POSSIBLE"))
    g = s["game"]
    if g:
        rows += [("blank", "", ""), ("head", "PROGRESS", ""),
                 ("line", "XP earned", f"+{g['xp']:,}"),
                 ("line", "Level", (f"{g['start_level']} → {g['level']}" if g["level"] != g["start_level"] else str(g["level"]))
                                    + (f" · {g['rank']}" if g["rank"] else ""))]
        if g["need"]:
            rows.append(("bar", "Next level", f"{g['into']:,} / {g['need']:,} XP", g["into"] / g["need"]))
        rows += [("line", "Intel Coins", f"+{g['coins']:,}  (balance {g['balance']:,})"),
                 ("line", "Streak", f"{g['streak']} day(s)  (best {g['best_streak']})"),
                 ("line", "Completed", f"{g['quests']} quests · {g['bounties']} bounties · {g['missions']} missions")]
        ms = s["milestones"]
        rows += [("blank", "", ""), ("head", "MILESTONES", "")]
        if ms and ms_limit > 0:
            rows += [("ms", x, "") for x in ms[-ms_limit:]]
            if len(ms) > ms_limit:
                rows.append(("ms", f"+{len(ms) - ms_limit} earlier", ""))
        else:
            rows.append(("ms", "No new milestones this session." if not ms else f"{len(ms)} milestone(s), see the session report.", ""))
    return rows

def session_outro() -> None:
    """Blocking. Plays the shutdown sound and shows the recap. Never leaves the terminal in a bad state."""
    play_shutdown_sound()
    from rich.console import Console
    console = Console()
    s = outro_stats()
    fd = sys.stdin.fileno()
    saved = termios.tcgetattr(fd)
    st = {"skip": False, "frac": 0.0, "shown": 0, "phase": 0, "done": False}

    def key_hit() -> bool:
        try:
            if select.select([fd], [], [], 0)[0]:
                os.read(fd, 64)
                return True
        except Exception:
            pass
        return False

    def wait(sec: float, hold: bool = False):
        end = time.time() + sec
        while time.time() < end:
            if key_hit():
                if hold:
                    st["done"] = True
                else:
                    st["skip"] = True
                return
            time.sleep(0.02)

    def frame():
        W, H = console.size
        max_h = 11 if H >= 38 else 5 if H >= 30 else 0
        banner = fx_big("SESSION COMPLETE", max(10, W - 12), max_h) if max_h else None
        brows = banner or []
        limit = 6
        rows = _outro_rows(s, limit)
        while limit > 0 and len(rows) + (len(brows) or 1) + 6 > H:
            limit -= 1
            rows = _outro_rows(s, limit)
        if len(rows) + (len(brows) or 1) + 6 > H:
            brows = []
        phase = st["phase"]
        out = []
        for r in brows:
            if not r.strip():
                out.append(Text(" " * len(r)))
                continue
            out.append(Text(r[: int(len(r) * st["frac"])].ljust(len(r)), style="bold bright_green" if phase % 2 == 0 else "bold green", no_wrap=True))
        if not brows:
            out.append(Text("S E S S I O N   C O M P L E T E"[: int(32 * st["frac"])].ljust(32), style="bold bright_green", no_wrap=True))
        g = s["game"]
        out.append(Text(f"Operator {g['name']}" if g and g["name"] else "scanner offline", style="dim green", no_wrap=True))
        out.append(Text(""))
        width = 58
        block = []
        for i, row in enumerate(rows[: st["shown"]]):
            kind, a, b = row[0], row[1], row[2]
            if kind == "blank":
                t = Text("")
            elif kind == "head":
                t = Text(f"▌{a}", style="bold bright_cyan")
            elif kind == "ms":
                t = Text(f"  ★ {a}", style="bright_yellow")
            elif kind == "bar":
                t = Text(f"  {a:<18}", style="green")
                t.append_text(mini_bar(row[3], 16, "green"))
                t.append(f" {b}", style="bright_white")
            else:
                t = Text(f"  {a:<18}", style="green")
                t.append(b, style="bold bright_white")
            t.truncate(width, overflow="ellipsis", pad=True)
            block.append(t)
        out.append(Align.center(Group(*block)))
        sub = "press a key to close" if st["shown"] >= len(rows) else "press a key to skip ahead"
        out.append(Text(""))
        out.append(Text(sub, style="dim"))
        return Panel(Align.center(Group(*[Align.center(x) if not isinstance(x, Align) else x for x in out]), vertical="middle"),
                     height=H, box=DOUBLE, border_style="bold bright_green" if phase % 2 == 0 else "green"), len(rows)

    try:
        tty.setcbreak(fd)
        with Live(console=console, screen=True, auto_refresh=False, transient=True) as live:
            for k in range(9):                                              # wipe the title in
                st["frac"], st["phase"] = k / 8, k
                live.update(frame()[0], refresh=True)
                wait(0.05)
                if st["skip"]:
                    break
            st["frac"] = 1.0
            total = frame()[1]
            for i in range(total):                                          # reveal the stats row by row
                st["shown"] = i + 1
                live.update(frame()[0], refresh=True)
                if not st["skip"]:
                    wait(0.07)
            st["shown"] = total
            live.update(frame()[0], refresh=True)
            end = time.time() + OUTRO_HOLD
            while not st["done"] and time.time() < end:
                st["phase"] = int(time.time() * 2)
                live.update(frame()[0], refresh=True)
                wait(0.25, hold=True)
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, saved)
        termios.tcflush(fd, termios.TCIFLUSH)

# =============================================================================
# ASYNC INPUT LISTENER & MAIN LOOP
# =============================================================================
@contextmanager
def line_mode():
    """Normal echoing, line-edited input for input() prompts.

    The dashboard keeps the terminal in cbreak mode (no echo), so without this you type blind.
    """
    if not HAVE_TTY:
        yield
        return
    fd = sys.stdin.fileno()
    saved = termios.tcgetattr(fd)
    cooked = termios.tcgetattr(fd)
    cooked[3] |= termios.ECHO | termios.ICANON
    termios.tcsetattr(fd, termios.TCSADRAIN, cooked)
    try:
        yield
    finally:
        termios.tcflush(fd, termios.TCIFLUSH)   # drop keys mashed while the prompt was up
        termios.tcsetattr(fd, termios.TCSADRAIN, saved)

def ask(prompt: str) -> str:
    """input() that treats Ctrl-C / Ctrl-D as 'cancel' instead of killing the scanner."""
    try:
        return input(prompt).strip()
    except (EOFError, KeyboardInterrupt):
        return ""

def parse_index(choice: str, n: int):
    try:
        v = int(choice)
    except ValueError:
        return None
    return v if 1 <= v <= n else None

def pick_device(title: str, cancel_msg: str):
    """Numbered device picker (strongest signal first). Returns (mac, message); mac is None if cancelled."""
    console = Console()
    now = time.time()
    rows = sorted(get_processed_devices(now), key=lambda d: d.ema, reverse=True)
    rows = rows[:max(5, console.size.height - 10)]
    sys.stdout.write("\033[H\033[J")
    if rows:
        table = Table(title=title, box=ROUNDED)
        table.add_column("#", justify="right", style="bold yellow")
        table.add_column("", width=1)
        table.add_column("Name")
        table.add_column("MAC", style="dim")
        table.add_column("RSSI", justify="right")
        for n, d in enumerate(rows, 1):
            live = now - d.last <= ACTIVE_WINDOW
            table.add_row(str(n), Text("●" if live else "○", style="green" if live else "dim"),
                          Text(display_name(d)), Text(d.mac), f"{d.ema:.0f}")
        console.print(table)
    else:
        console.print("[dim]No devices on screen yet. You can still type a MAC address.[/]")

    choice = ask("Device number or MAC address (blank to cancel): ")
    if not choice:
        return None, cancel_msg
    idx = parse_index(choice, len(rows))
    if idx:
        return rows[idx - 1].mac, ""
    typed = choice.upper()
    dashed = typed.replace("-", ":")
    if typed in DEVICES:
        return typed, ""
    if MAC_RE.match(dashed):
        return dashed, ""
    return None, f"'{clean(choice, 24)}' is neither a number from the list nor a valid MAC. Nothing selected."

def ignore_flow() -> str:
    """Hide a device by MAC or by advertised-name pattern; '-<text>' undoes one; 'list' shows everything ignored."""
    if not KNOWN:
        return "Known-devices file isn't loaded."
    print("Ignore a device\n")
    print("  AA:BB:CC:DD:EE:FF   one device, by MAC")
    print("  My Speaker          every device with exactly that name or label (case-insensitive)")
    print("  *Find My*           wildcards:  * ? [abc]   matches part of a name, e.g. *TV*  or  Galaxy*")
    print("  re:^(Tile|Smart)    a regular expression")
    print("  -<any of the above> stop ignoring it        list   show what is ignored\n")
    raw = ask("Ignore: ")
    if not raw:
        return "Cancelled."
    if raw.lower() == "list":
        rows = [("MAC", m, "saved") for m in sorted(KNOWN.ignored)] + [("MAC", m, "config") for m in sorted(CFG_IGNORE)]
        rows += [("name", n, "saved") for n in KNOWN.ignored_names] + [("name", n, "config") for n in CFG_IGNORE_NAMES]
        rows += [("name", n, "this run (--ignore-name)") for n in SESSION_IGNORE_NAMES]
        print()
        for kind, val, src in rows:
            print(f"  {kind:<5} {val:<40} {src}")
        if not rows:
            print("  Nothing is ignored.")
        ask("\nPress Enter to return. ")
        return f"{len(rows)} ignore rule(s)."
    remove = raw.startswith("-")
    text = (raw[1:] if remove else raw).strip()
    if not text:
        return "Cancelled."
    if text[:3].lower() == "re:":
        try:
            re.compile(text[3:])
        except re.error as e:
            return f"Invalid regular expression: {e}"
    is_mac = bool(MAC_RE.match(text.upper()))
    if remove:
        if is_mac:
            if text.upper() in KNOWN.ignored:
                KNOWN.ignored.discard(text.upper())
                KNOWN.save()
                return f"No longer ignoring {text.upper()} (it will reappear when it next advertises)."
            return "That MAC isn't in your saved ignore list" + (" (it comes from the config file)." if text.upper() in CFG_IGNORE else ".")
        hit = next((n for n in KNOWN.ignored_names if n.lower() == text.lower()), None)
        if hit:
            KNOWN.ignored_names.remove(hit)
            NAME_IGNORED_MACS.clear()                  # re-evaluated from the next packet on
            KNOWN.save()
            return f"No longer ignoring name '{hit}'."
        where = " (it comes from the config file or --ignore-name; edit those instead)." if text in CFG_IGNORE_NAMES or text in SESSION_IGNORE_NAMES else "."
        return "That name pattern isn't in your saved ignore list" + where
    if is_mac:
        mac = text.upper()
        KNOWN.ignored.add(mac)
        KNOWN.save()
        purge_device(mac)
        return f"Permanently ignored device {mac}"
    if not any(n.lower() == text.lower() for n in KNOWN.ignored_names):
        KNOWN.ignored_names.append(text)
        KNOWN.save()
    n = purge_name_matches()
    return f"Permanently ignoring names matching '{text}' ({n} device{'s' if n != 1 else ''} hidden now)"

def rename_flow() -> str:
    """Rename a device by picking it from a numbered list. Returns a status-line message."""
    mac, msg = pick_device("Rename which device?  (strongest signal first)", "Rename cancelled.")
    if not mac:
        return msg
    current = KNOWN.renames.get(mac)
    hint = f" (currently '{current}')" if current else ""
    new_name = clean(ask(f"New name for {mac}{hint}. Blank = cancel, '-' = clear: "), 40)
    if not new_name:
        return "Rename cancelled."
    if new_name == "-":
        if KNOWN.renames.pop(mac, None) is None:
            return f"{mac} has no custom name to clear."
        KNOWN.save()
        if mac in DEVICES:
            DEVICES[mac].fp = None                       # re-identify on the next packet
        return f"Cleared custom name for {mac}"
    KNOWN.renames[mac] = new_name
    KNOWN.save()
    if mac in DEVICES:
        DEVICES[mac].fp = None                           # re-identify on the next packet, now that it has a name
    game_bump("devices_renamed")
    return f"Permanently renamed {mac} to '{new_name}'"

def hunt_flow() -> str:
    mac, msg = pick_device("Hunt which device?  (the one you want to find)", "Hunt cancelled.")
    if not mac:
        return msg
    start_hunt(mac)
    dev = DEVICES.get(mac)
    note = " (rotating address: the hunt can lose it)" if dev and dev.kind in ("private-resolvable", "private-nonresolvable", "random") else ""
    return f"Hunting {mac}{note}. Walk toward a stronger signal. e ends the hunt."

def trust_flow() -> str:
    """Mark a tracker from Follower Watch as yours so it stops alerting."""
    rows = follow_rows()
    if not rows:
        return "No trackers are being followed yet."
    console = Console()
    sys.stdout.write("\033[H\033[J")
    table = Table(title="Which tracker is yours?", box=ROUNDED)
    table.add_column("#", justify="right", style="bold yellow")
    table.add_column("Level")
    table.add_column("Tracker")
    table.add_column("MAC", style="dim")
    table.add_column("Near you", justify="right")
    for n, t in enumerate(rows, 1):
        table.add_row(str(n), FOLLOW_STYLE[t.tier][0], t.label or "Tracker", t.mac, fmt_dur(t.near_s))
    console.print(table)
    idx = parse_index(ask("Number of the tracker that's yours (blank to cancel): "), len(rows))
    if not idx:
        return "Cancelled. Nothing changed."
    mac = rows[idx - 1].mac
    KNOWN.trusted.add(mac)
    KNOWN.save()
    TAILS.pop(mac, None)
    return f"Marked {mac} as yours. It won't trigger follower alerts."

def inspect_flow() -> str:
    """Pick a device from the numbered list (or type a MAC) and open the inspector on it."""
    mac, msg = pick_device("Inspect which device?  (strongest signal first)", "Inspect cancelled.")
    if not mac:
        return msg
    INSPECT["mac"] = mac
    open_overlay("inspect")
    return f"Inspecting {mac}. c closes, Enter picks another device."

def view_flow() -> str:
    """Pick any view (base, security, or a single category) from a numbered list."""
    views = view_list()
    console = Console()
    sys.stdout.write("\033[H\033[J")
    table = Table(title="Switch to which view?", box=ROUNDED)
    half = math.ceil(len(views) / 2)                 # two side-by-side columns so the list fits a small terminal
    for _ in range(2):
        table.add_column("#", justify="right", style="bold yellow")
        table.add_column("View", no_wrap=True)
    def cell(n):
        if n > len(views):
            return "", ""
        mark = "  ◀" if n - 1 == CFG["view_mode"] else ""
        return str(n), views[n - 1][1] + mark
    for r in range(1, half + 1):
        table.add_row(*cell(r), *cell(r + half))
    console.print(table)
    idx = parse_index(ask("View number (blank to cancel): "), len(views))
    if not idx:
        return "View unchanged."
    CFG["view_mode"] = idx - 1
    close_overlays()
    return f"View {idx}/{len(views)}: {views[idx - 1][1]}"

OVERLAYS = ("help", "follow", "hunt", "inspect", "profile", "tutorial", "missions")

def toggle_overlay(name: str):
    """Open/close one full-screen panel; opening one closes the rest."""
    key = f"show_{name}"
    new = not CFG[key]
    for o in OVERLAYS:
        CFG[f"show_{o}"] = False
    CFG[key] = new

def open_overlay(name: str):
    """Show one full-screen panel (never toggles it off), closing the rest."""
    for o in OVERLAYS:
        CFG[f"show_{o}"] = (o == name)

async def input_listener(stop_event, queue):
    if not HAVE_TTY:
        return
    fd = sys.stdin.fileno()
    old_settings = termios.tcgetattr(fd)
    tty.setcbreak(fd)
    try:
        while not stop_event.is_set():
            if select.select([fd], [], [], 0.1)[0]:
                # Read raw bytes (not sys.stdin.read) so buffered text I/O can't hide the
                # rest of an arrow-key escape sequence from select().
                data = os.read(fd, 64).decode("utf-8", errors="ignore")
                i = 0
                while i < len(data):
                    ch = data[i]
                    i += 1
                    if ch != "\x1b":
                        await queue.put(ch)
                        continue
                    if i >= len(data) or data[i] not in "[O":
                        await queue.put("\x1b")              # a lone Esc press still quits
                        continue
                    i += 1                                    # skip '[' / 'O'
                    start = i
                    while i < len(data) and not ("@" <= data[i] <= "~"):
                        i += 1                                # parameter bytes
                    final = data[i] if i < len(data) else ""
                    i += 1
                    if final == "C" and i - 1 == start:
                        await queue.put("RIGHT")
                    elif final == "D" and i - 1 == start:
                        await queue.put("LEFT")
                    elif final == "A" and i - 1 == start:
                        await queue.put("UP")
                    elif final == "B" and i - 1 == start:
                        await queue.put("DOWN")
                    # any other escape sequence (up/down, F-keys, ...) is ignored
            await asyncio.sleep(0.05)
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)

# =============================================================================
# CLASSIC BLUETOOTH (BR/EDR) DISCOVERY  (key k, or --classic)
# bleak only sees Bluetooth Low Energy. Older devices (car stereos, speakers, headsets, some phones and
# laptops in discoverable mode) use classic Bluetooth. This opens a second BlueZ discovery session over D-Bus
# that asks for classic devices only, and feeds every response into the same device list. Linux / BlueZ only.
# Classic devices answer an inquiry only while they are discoverable, and inquiry shares the radio with the LE
# scan, so expect slower updates while it is on. It is paused automatically during a connect probe.
# =============================================================================
CLASSIC = {"on": False, "bus": None, "adapter": None, "paused": False, "heard": set()}

COD_MAJOR = {1: ("laptops_tablets", "Computer"), 2: ("smartphones", "Phone"), 3: ("networking_mesh", "Network access point"),
             4: ("wearables_audio", "Audio / video"), 5: ("other", "Peripheral"), 6: ("other", "Imaging"),
             7: ("wearables_audio", "Wearable"), 8: ("handhelds_gaming", "Toy"), 9: ("medical_health", "Health device")}
COD_AUDIO = {1: "Headset", 2: "Hands-free", 4: "Microphone", 5: "Loudspeaker", 6: "Headphones", 7: "Portable audio",
             8: "Car audio", 9: "Set-top box", 10: "HiFi audio", 11: "VCR", 12: "Video camera", 13: "Camcorder",
             14: "Video monitor", 15: "Video display + speaker", 16: "Video conferencing", 18: "Gaming / toy"}
COD_COMPUTER = {1: "Desktop", 2: "Server", 3: "Laptop", 4: "Handheld PC", 5: "Palm PC", 6: "Wearable computer", 7: "Tablet"}
COD_PHONE = {1: "Cellular", 2: "Cordless", 3: "Smartphone", 4: "Wired modem", 5: "Common ISDN"}
COD_WEARABLE = {1: "Wristwatch", 2: "Pager", 3: "Jacket", 4: "Helmet", 5: "Glasses"}

def cod_info(cod: int):
    """(scanner category, readable description) from a Class-of-Device value."""
    major, minor = (cod >> 8) & 0x1F, (cod >> 2) & 0x3F
    cat, label = COD_MAJOR.get(major, ("other", "Unclassified"))
    sub = {4: COD_AUDIO, 1: COD_COMPUTER, 2: COD_PHONE, 7: COD_WEARABLE}.get(major, {}).get(minor, "")
    if major == 5:
        sub = {1: "Keyboard", 2: "Mouse / pointer", 3: "Keyboard + pointer"}.get(minor >> 4 & 3, "")
        if (minor & 0xF) == 1:
            sub = "Joystick"
        elif (minor & 0xF) == 2:
            sub = "Gamepad"
    if major == 6:
        sub = "/".join(n for m, n in ((0x10, "Display"), (0x20, "Camera"), (0x40, "Scanner"), (0x80, "Printer")) if cod & m)
    if major == 4 and minor == 8:
        cat = "auto_aerial"
    return cat, (f"{label}: {sub}" if sub else label)

def classic_supported() -> str:
    if not sys.platform.startswith("linux"):
        return "Classic Bluetooth discovery needs Linux with BlueZ."
    try:
        import dbus_fast  # noqa: F401
    except ImportError:
        return "Classic discovery needs the dbus-fast package (pip install dbus-fast)."
    return ""

class _CDev:
    def __init__(self, address, name):
        self.address, self.name = address, name
        self.details = {"props": {"AddressType": "public"}}

def classic_feed(p: dict):
    """One classic device's BlueZ properties -> the normal detection path, then label it from its Class of Device."""
    cod, addr, rssi = p.get("Class"), p.get("Address"), p.get("RSSI")
    if cod is None or not addr or rssi is None:
        return
    adv = types.SimpleNamespace(rssi=int(rssi), local_name=p.get("Name") or "", manufacturer_data={},
                                service_data={}, service_uuids=list(p.get("UUIDs") or []), tx_power=p.get("TxPower"))
    on_detect(_CDev(addr.upper(), p.get("Name") or ""), adv)
    dev = DEVICES.get(addr.upper())
    if dev is None:
        return
    cat, desc = cod_info(int(cod))
    dev.classic, dev.cod = True, int(cod)
    i = dev.ident
    i.addr_type = "classic (BR/EDR)"
    if not i.tier and not i.known and i.category in ("other", "anonymous"):
        i.category = cat
    if not i.label:
        i.label = f"Classic BT · {desc}"
    if not any("Class of Device" in r for r in i.reasons):
        i.reasons.append(f"Class of Device 0x{int(cod):06X} ({desc})")
    CLASSIC["heard"].add(addr.upper())

def _dbus_unwrap(d: dict) -> dict:
    return {k: getattr(v, "value", v) for k, v in d.items()}

async def _classic_begin():
    from dbus_fast import Variant
    ad = CLASSIC["adapter"]
    await ad.call_set_discovery_filter({"Transport": Variant("s", "bredr")})
    await ad.call_start_discovery()

async def classic_start() -> str:
    why = classic_supported()
    if why:
        CFG["classic"] = False
        return why
    bus = None
    try:
        from dbus_fast.aio import MessageBus
        from dbus_fast import BusType, Message, MessageType
        bus = await MessageBus(bus_type=BusType.SYSTEM).connect()
        base = f"/org/bluez/{ADAPTER['name']}"
        state: dict = {}

        def handle(msg):
            if msg.message_type != MessageType.SIGNAL:
                return
            try:
                if msg.member == "InterfacesAdded" and msg.path == "/":
                    opath, ifaces = msg.body
                    if opath.startswith(base + "/dev_") and "org.bluez.Device1" in ifaces:
                        props = _dbus_unwrap(ifaces["org.bluez.Device1"])
                        if "Class" in props:
                            state.setdefault(opath, {}).update(props)
                            classic_feed(state[opath])
                elif msg.member == "PropertiesChanged" and msg.path.startswith(base + "/dev_"):
                    iface, changed, _ = msg.body
                    if iface != "org.bluez.Device1":
                        return
                    props = _dbus_unwrap(changed)
                    if msg.path not in state:
                        if "Class" not in props:
                            return                        # an LE-only device: not ours
                        state[msg.path] = {"Address": msg.path.rsplit("dev_", 1)[1].replace("_", ":")}
                    state[msg.path].update(props)
                    if "RSSI" in props:                   # only live responses; BlueZ keeps stale cached devices around
                        classic_feed(state[msg.path])
            except Exception:
                pass

        bus.add_message_handler(handle)
        reply = await bus.call(Message(destination="org.freedesktop.DBus", path="/org/freedesktop/DBus",
                                       interface="org.freedesktop.DBus", member="AddMatch", signature="s",
                                       body=["type='signal',sender='org.bluez'"]))
        if reply.message_type == MessageType.ERROR:
            raise RuntimeError(str(reply.body))
        intro = await bus.introspect("org.bluez", base)
        CLASSIC["adapter"] = bus.get_proxy_object("org.bluez", base, intro).get_interface("org.bluez.Adapter1")
        CLASSIC["bus"] = bus
        await _classic_begin()
    except Exception as e:
        try:
            if bus is not None:
                bus.disconnect()
        except Exception:
            pass
        CLASSIC.update(bus=None, adapter=None, on=False)
        CFG["classic"] = False
        return f"Classic discovery failed: {clean(str(e) or e.__class__.__name__, 90)}"
    CLASSIC.update(on=True, paused=False)
    CFG["classic"] = True
    log_event("Classic Bluetooth discovery started")
    return "Classic Bluetooth discovery ON (devices must be discoverable to answer)."

async def classic_stop(quiet: bool = False) -> str:
    ad, bus = CLASSIC["adapter"], CLASSIC["bus"]
    try:
        if ad is not None and not CLASSIC["paused"]:
            await ad.call_stop_discovery()
    except Exception:
        pass
    try:
        if bus is not None:
            bus.disconnect()
    except Exception:
        pass
    was = CLASSIC["on"]
    CLASSIC.update(on=False, bus=None, adapter=None, paused=False)
    if was and not quiet:
        log_event("Classic Bluetooth discovery stopped")
    return "Classic Bluetooth discovery OFF."

async def classic_toggle() -> str:
    if CLASSIC["on"]:
        msg = await classic_stop()
        CFG["classic"] = False
    else:
        msg = await classic_start()
    save_settings()
    return msg

async def classic_pause() -> bool:
    """Stop classic inquiry (used while a connect probe runs). Returns True if it was running."""
    if CLASSIC["on"] and CLASSIC["adapter"] is not None and not CLASSIC["paused"]:
        try:
            await CLASSIC["adapter"].call_stop_discovery()
            CLASSIC["paused"] = True
            return True
        except Exception:
            pass
    return False

async def classic_resume():
    if CLASSIC["on"] and CLASSIC["paused"]:
        try:
            await _classic_begin()
        except Exception:
            pass
        CLASSIC["paused"] = False

async def amain(args):
    console = Console()
    scanner = bleak.BleakScanner(detection_callback=on_detect, scanning_mode="active", bluez={"adapter": ADAPTER["name"]})
    try:
        await scanner.start()
    except Exception as e:
        console.print(f"[red]Could not start BLE scan:[/red] {e}")
        if sys.platform.startswith("linux"):
            console.print(f"[dim]Tried Bluetooth adapter {ADAPTER['name']}. Pick another with --adapter hci0 (list them with: hciconfig).[/dim]")
        return

    SCAN["scanner"] = scanner
    if BOOT["pending"]:                                   # the adapter really started, so the staged handshake is honest
        BOOT["pending"] = False
        try:
            await asyncio.to_thread(boot_sequence, console, BOOT["cfg_status"])
        except Exception:
            pass
    if CFG["classic"]:
        STATUS.set(await classic_start())
    stop = asyncio.Event()
    key_queue = asyncio.Queue()
    input_task = asyncio.create_task(input_listener(stop, key_queue)) if HAVE_TTY else None

    live = Live(console=console, screen=True, auto_refresh=False)
    live.start()
    try:
        while not stop.is_set():
            while not key_queue.empty():
                ch = key_queue.get_nowait()
                if ch in ('q', 'Q', '\x1b'):
                    stop.set()
                elif ch in ('m', 'M'):
                    global MUTED
                    MUTED = not MUTED
                    STATUS.set(f"Sound notifications: {'MUTED' if MUTED else 'UNMUTED'}")
                elif ch in ('n', 'N'):
                    NOTIFY["idx"] = (NOTIFY["idx"] + (1 if ch == 'n' else -1)) % len(NOTIFY_SOUNDS)
                    save_settings()
                    snd, label = NOTIFY_SOUNDS[NOTIFY["idx"]]
                    STATUS.set(f"New-device sound: {label}" if snd else "New-device sound: OFF")
                    if snd:
                        play_notification_sound(snd)                       # preview
                elif ch in ('z', 'Z'):
                    CFG["fx"] = not CFG["fx"]
                    save_settings()
                    STATUS.set(f"Visual effects (celebrations, flash, pulse, radar, sonar, heartbeat, XP shimmer): {'ON' if CFG['fx'] else 'OFF'}")
                elif ch in ('o', 'O'):
                    CFG["crt"] = not CFG["crt"]
                    save_settings()
                    STATUS.set(f"CRT scanlines: {'ON' if CFG['crt'] else 'OFF'}")
                elif ch == ' ' and FX["cur"]:
                    fx_skip()
                elif ch in (MISSION_KEY, MISSION_KEY.upper()) and not CFG["show_inspect"]:   # (with the inspector open, y connects to that device)
                    mission_key()
                elif CFG["show_missions"] and (ch in ('RIGHT', 'LEFT') or (len(ch) == 1 and ch.isdigit())):
                    msg = mission_nav(ch)
                    if msg:
                        STATUS.set(msg)
                elif ch in ('p', 'P'):
                    game_profile_key()
                elif ch in ('u', 'U'):
                    CFG["auto_tactical"] = not CFG["auto_tactical"]
                    AUTO["pending"] = None
                    save_settings()
                    STATUS.set(f"Auto-switch to Tactical view on new tactical device: {'ON' if CFG['auto_tactical'] else 'OFF'}")
                elif ch == '$':
                    live.stop()
                    with line_mode():
                        STATUS.set(donate_flow())
                    reset_tick()
                    live.start()
                elif ch in ('t', 'T'):
                    live.stop()
                    with line_mode():
                        STATUS.set(title_flow())
                    reset_tick()
                    live.start()
                elif ch in ('b', 'B'):
                    tutorial_key()
                elif CFG["show_tutorial"] and (ch in ('RIGHT', 'LEFT', 'UP', 'DOWN', 'j', 'k') or (len(ch) == 1 and ch.isdigit())):
                    tutorial_nav(ch)
                elif CFG["show_profile"] and ch in ('RIGHT', 'LEFT', 'UP', 'DOWN', 'j', 'k'):
                    game_profile_nav(ch)
                elif ch in ('d', 'D'):
                    CFG["dedup"] = not CFG["dedup"]
                    STATUS.set(f"MAC Deduplication (Collapsing): {'ON' if CFG['dedup'] else 'OFF'}")
                elif ch == '[':
                    step_min_rssi(-1)
                elif ch == ']':
                    step_min_rssi(+1)
                elif ch in ('l', 'L'):
                    live.stop()
                    sys.stdout.write("\033[H\033[J")
                    with line_mode():
                        raw = input(f"Minimum signal in dBm (now {CFG['min_rssi'] if CFG['min_rssi'] is not None else 'off'}; e.g. -75, blank or 0 = off): ").strip()
                    STATUS.set(apply_signal_input(raw))
                    reset_tick()
                    live.start()
                elif ch in ('a', 'A'):
                    CFG["rssi_bypass"] = not CFG["rssi_bypass"]
                    save_settings()
                    STATUS.set(f"Alerts / known / hunted bypass the signal filter: {'ON' if CFG['rssi_bypass'] else 'OFF'}")
                elif ch in ('r', 'R'):
                    live.stop()
                    with line_mode():
                        STATUS.set(rename_flow())
                    reset_tick()
                    live.start()
                elif ch in ('i', 'I'):
                    live.stop()
                    sys.stdout.write("\033[H\033[J")
                    with line_mode():
                        STATUS.set(ignore_flow())
                    reset_tick()
                    live.start()
                elif ch in ('s', 'S') and probe_active():
                    STATUS.set("A connect probe is running; scanning resumes automatically when it finishes.")
                elif ch in ('s', 'S'):
                    CFG["scanning"] = not CFG["scanning"]
                    if CFG["scanning"]:
                        await scanner.start()
                        log_event("Scanning resumed")
                        STATUS.set("Scanning RESUMED")
                    else:
                        await scanner.stop()
                        log_event("Scanning paused")
                        STATUS.set("Scanning PAUSED")
                elif ch in ('f', 'F'):
                    toggle_overlay("follow")
                    STATUS.set("Toggled Follower Watch")
                elif ch in ('x', 'X'):
                    live.stop()
                    with line_mode():
                        STATUS.set(trust_flow())
                    reset_tick()
                    live.start()
                elif ch in ('g', 'G'):
                    if hunting():
                        toggle_overlay("hunt")
                    else:
                        live.stop()
                        with line_mode():
                            STATUS.set(hunt_flow())
                        reset_tick()
                        live.start()
                        if hunting():
                            toggle_overlay("hunt")
                elif ch in ('e', 'E') and CFG["show_hunt"]:
                    stop_hunt()
                    STATUS.set("Hunt ended.")
                elif ch in ('e', 'E'):
                    live.stop()
                    with line_mode():
                        STATUS.set(shop_flow())
                    reset_tick()
                    live.start()
                elif ch in ('c', 'C', '\r', '\n'):
                    if CFG["show_inspect"] and ch in ('c', 'C'):
                        toggle_overlay("inspect")
                        STATUS.set("Closed device inspector")
                    else:
                        live.stop()
                        with line_mode():
                            STATUS.set(inspect_flow())
                        reset_tick()
                        live.start()
                elif ch in ('y', 'Y'):
                    STATUS.set(start_probe())
                elif ch in ('k', 'K'):
                    STATUS.set("Starting classic Bluetooth discovery..." if not CLASSIC["on"] else "Stopping classic discovery...")
                    STATUS.set(await classic_toggle())
                elif ch in ('h', 'H', '?'):
                    toggle_overlay("help")
                    STATUS.set("Toggled Help & Shortcuts View")
                elif ch in ('v', 'V', 'RIGHT', 'LEFT'):
                    views = view_list()
                    CFG["view_mode"] = (CFG["view_mode"] + (-1 if ch in ('LEFT', 'V') else 1)) % len(views)
                    close_overlays()
                    STATUS.set(f"View {CFG['view_mode'] + 1}/{len(views)}: {views[CFG['view_mode']][1]}")
                elif ch in ('w', 'W'):
                    live.stop()
                    with line_mode():
                        STATUS.set(view_flow())
                    reset_tick()
                    live.start()

            now = time.time()
            dt = tick_scan_time(now, CFG["scanning"])
            follow_tick(now, dt)
            hunt_tick(now)
            count_tick(now)
            auto_tactical_tick()
            prune_ghosts(now)
            game_tick(now, dt)
            mission_tick(now, dt)
            fx_tick(now)
            heart_tick(now)
            xp_anim_tick(now)
            live.update(build_dashboard(console.size), refresh=True)
            await asyncio.sleep(0.1 if fx_active() else 0.08 if glitch_live(now) else ANIM_TICK if anim_active(now) else 0.25)
    except asyncio.CancelledError:
        pass
    finally:
        if input_task:
            input_task.cancel()
        live.stop()
        try:
            await classic_stop(quiet=True)
        except Exception:
            pass
        try:
            if scanner._is_running:
                await scanner.stop()
        except Exception:
            pass

# =============================================================================
# END-OF-SESSION HTML REPORT
# Written automatically on exit (quit key, Ctrl+C, or a crash after scanning began).
# One self-contained file: inline CSS/JS, no network, every radio-supplied string escaped.
# =============================================================================
REPORT_DIR = "session_logs"

REPORT_CSS = """
:root{--bg:#f6f7f9;--card:#fff;--ink:#1c2230;--mut:#667085;--line:#e3e6ec;--acc:#0f7bb5;--bar:#0f7bb5;
--red:#c62828;--orange:#d9730d;--purple:#7b3fb3;--blue:#1565c0;--green:#2e7d32}
@media (prefers-color-scheme:dark){:root{--bg:#10141b;--card:#181e28;--ink:#e6e9ef;--mut:#8b95a7;--line:#2a3242;
--acc:#4db3e6;--bar:#4db3e6;--red:#ef6a6a;--orange:#f0a050;--purple:#b98be0;--blue:#6aa9f0;--green:#6fcf7a}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:14px/1.5 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
main{max-width:1180px;margin:0 auto;padding:24px 16px 48px}
h1{font-size:22px;margin:0 0 2px}h2{font-size:16px;margin:0 0 12px}
.sub{color:var(--mut);margin:0 0 20px}.muted{color:var(--mut)}
section{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:16px;margin:0 0 16px}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px}
.card{border:1px solid var(--line);border-radius:8px;padding:10px 12px}
.card b{display:block;font-size:20px;line-height:1.2}.card span{color:var(--mut);font-size:12px}
.grid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(320px,1fr));gap:16px}
.bars .bar{display:grid;grid-template-columns:minmax(90px,200px) 1fr 44px;gap:8px;align-items:center;margin:3px 0}
.bl{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.bt{background:var(--line);height:10px;border-radius:5px;overflow:hidden}
.bt i{display:block;height:100%;background:var(--bar)}.bn{text-align:right;color:var(--mut)}
.tw{overflow-x:auto}table{border-collapse:collapse;width:100%;font-size:13px}
th,td{text-align:left;padding:6px 8px;border-bottom:1px solid var(--line);white-space:nowrap}
td.w{white-space:normal;min-width:200px}th{color:var(--mut);font-weight:600;position:sticky;top:0;background:var(--card)}
table.s th{cursor:pointer}table.s th:hover{color:var(--acc)}
.tag{display:inline-block;padding:1px 8px;border-radius:10px;font-size:11px;font-weight:700;border:1px solid currentColor}
.t-alert{color:var(--red)}.t-possible,.t-follower{color:var(--orange)}.t-watchlist,.t-game{color:var(--purple)}
.t-notice,.t-info{color:var(--blue)}.t-hunt{color:var(--green)}
code{font:12px ui-monospace,Menlo,Consolas,monospace}
input{width:100%;max-width:340px;padding:6px 10px;border:1px solid var(--line);border-radius:6px;background:var(--bg);color:var(--ink);margin:0 0 10px}
.tl{list-style:none;margin:0;padding:0}.tl li{display:grid;grid-template-columns:70px 90px 1fr;gap:8px;padding:5px 0;border-bottom:1px solid var(--line)}
footer{color:var(--mut);font-size:12px;margin-top:20px}
@media print{body{background:#fff}section{break-inside:avoid}}
"""

REPORT_JS = """
document.querySelectorAll('table.s').forEach(function(t){
  t.querySelectorAll('th').forEach(function(th,i){
    th.addEventListener('click',function(){
      var asc=th.dataset.asc!=='1';t.querySelectorAll('th').forEach(function(x){delete x.dataset.asc});th.dataset.asc=asc?'1':'0';
      var rows=Array.from(t.tBodies[0].rows);
      rows.sort(function(a,b){var x=a.cells[i].dataset.s,y=b.cells[i].dataset.s,nx=parseFloat(x),ny=parseFloat(y);
        var c=(!isNaN(nx)&&!isNaN(ny))?nx-ny:String(x).localeCompare(String(y));return asc?c:-c});
      rows.forEach(function(r){t.tBodies[0].appendChild(r)});
    });
  });
});
var f=document.getElementById('flt');
if(f){f.addEventListener('input',function(){var q=f.value.toLowerCase();
  document.querySelectorAll('#devtbl tbody tr').forEach(function(r){r.style.display=r.textContent.toLowerCase().indexOf(q)<0?'none':''})})}
"""

REPORT_LEVELS = {"alert": "ALERT", "possible": "POSSIBLE", "follower": "FOLLOWER", "watchlist": "WATCHLIST", "notice": "NOTICE"}

def _e(s) -> str:
    return html_lib.escape(str(s if s is not None else ""), quote=True)

def _ts(t, date=False) -> str:
    if not t:
        return "—"
    return datetime.datetime.fromtimestamp(t).strftime("%Y-%m-%d %H:%M:%S" if date else "%H:%M:%S")

def _tag(level: str, text: str = "") -> str:
    return f'<span class="tag t-{_e(level)}">{_e(text or level.upper())}</span>'

def _bars(items) -> str:
    items = [(l, n) for l, n in items]
    if not items:
        return '<p class="muted">Nothing recorded.</p>'
    top = max(n for _, n in items) or 1
    rows = "".join(
        f'<div class="bar"><span class="bl" title="{_e(l)}">{_e(l)}</span>'
        f'<span class="bt"><i style="width:{max(2, 100 * n / top):.0f}%"></i></span><span class="bn">{n}</span></div>'
        for l, n in items)
    return f'<div class="bars">{rows}</div>'

def _cards(pairs) -> str:
    return '<div class="cards">' + "".join(
        f'<div class="card"><b>{_e(v)}</b><span>{_e(k)}</span></div>' for k, v in pairs) + "</div>"

def _table(headers, rows, sortable=True, tid="") -> str:
    """rows: list of lists; a cell is trusted HTML str, or (html, sort_key)."""
    head = "".join(f"<th>{_e(h)}</th>" for h in headers)
    body = []
    for r in rows:
        tds = []
        for c in r:
            h, k = c if isinstance(c, tuple) else (c, re.sub(r"<[^>]+>", "", str(c)))
            tds.append(f'<td data-s="{_e(k)}">{h}</td>')
        body.append("<tr>" + "".join(tds) + "</tr>")
    cls = ' class="s"' if sortable else ""
    idattr = f' id="{tid}"' if tid else ""
    return f'<div class="tw"><table{cls}{idattr}><thead><tr>{head}</tr></thead><tbody>{"".join(body)}</tbody></table></div>'

def _section(title, body) -> str:
    return f"<section><h2>{_e(title)}</h2>{body}</section>"

def report_devices() -> list:
    """Everything that cleared the signal filter at some point (the 'seen' total), oldest first."""
    return sorted((d for d in DEVICES.values() if d.counted), key=lambda d: d.first)

def report_security(devs) -> list:
    """Whole-session version of security_rows(): (level, device), most severe first."""
    rows = []
    for dev in devs:
        i = dev.ident
        if KNOWN and dev.mac in KNOWN.trusted:
            continue
        if i.known and not i.known_alert:
            continue
        tail = TAILS.get(dev.mac)
        if i.known and i.known_alert:
            level = "watchlist"
        elif i.tier == "alert":
            level = "alert"
        elif i.tier == "possible":
            level = "possible"
        elif tail and FOLLOW_RANK[tail.tier] >= 2:
            level = "follower"
        elif i.category in SECURITY_CATS:
            level = "notice"
        else:
            continue
        rows.append((level, dev))
    rows.sort(key=lambda r: (SECURITY_ORDER.index(r[0]), -r[1].peak))
    return rows

def _arrival_items(devs, start, end):
    span = max(60.0, end - start)
    step = 60 if span <= 1800 else 300 if span <= 10800 else 900
    n = int(span // step) + 1
    counts = [0] * n
    for d in devs:
        counts[min(n - 1, max(0, int((d.first - start) // step)))] += 1
    return [(datetime.datetime.fromtimestamp(start + i * step).strftime("%H:%M"), c) for i, c in enumerate(counts)]

def build_session_report(start: float, end: float) -> str:
    devs = report_devices()
    sec = report_security(devs)
    level_of = {d.mac: lvl for lvl, d in sec}
    wall = max(0.0, end - start)
    scan_s = SESSION["scan_seconds"]
    lv_n = collections.Counter(l for l, _ in sec)
    ghosts = [g for g in list(ARCHIVED_GHOSTS) + list(GHOSTS.values()) if len(g.macs) > 1]
    rotations = sum(g.rotations for g in ghosts)
    below = len(DEVICES) - len(devs)
    thr = CFG["min_rssi"]
    flt = "off" if thr is None else f"≥ {thr} dBm"
    adapter = " ".join(x for x in (ADAPTER.get("name", ""), ADAPTER.get("product", "")) if x) or "unknown"

    cards = _cards([
        ("Devices seen", len(devs)), ("Packets received", f"{STATS['packets']:,}"),
        ("Scan time", fmt_dur(scan_s)), ("Session length", fmt_dur(wall)),
        ("Avg packets/s", f"{STATS['packets'] / scan_s:.0f}" if scan_s > 1 else "—"),
        ("Security flags", len(sec)), ("Follower alerts", sum(1 for t in TAILS.values() if FOLLOW_RANK[t.tier] >= 2)),
        ("Rotating identities", len(ghosts)), ("MAC rotations linked", rotations),
    ])
    meta = _table(["Setting", "Value"], [
        ["Started", _e(_ts(start, True))], ["Ended", _e(_ts(end, True))],
        ["Bluetooth adapter", _e(adapter)], ["Version", _e(VERSION)],
        ["Signal filter at exit", _e(flt) + (f" ({below} tracked devices below it, not listed)" if below else "")],
        ["Alerts bypass filter", "yes" if CFG["rssi_bypass"] else "no"],
        ["MAC dedup", "on" if CFG["dedup"] else "off"], ["Follower scope", _e(FOLLOW["scope"])],
        ["Sound", "muted" if MUTED else "on"],
    ], sortable=False)

    cat_n = collections.Counter(d.ident.category for d in devs)
    cat_items = sorted(((f"{cat_meta(k)[0]} {cat_meta(k)[1]}", n) for k, n in cat_n.items()), key=lambda x: -x[1])
    ven_items = collections.Counter(clean(d.ident.vendor, 28) for d in devs if d.ident.vendor).most_common(12)
    addr_items = collections.Counter(d.ident.addr_type for d in devs).most_common()
    bins = [("strong ≥ -55", -55, 1), ("good -55…-67", -67, -55), ("fair -67…-80", -80, -67),
            ("weak -80…-90", -90, -80), ("faint < -90", -200, -90)]
    sig_items = [(label, sum(1 for d in devs if lo <= d.peak < hi)) for label, lo, hi in bins]

    if sec:
        sec_rows = []
        for lvl, d in sec:
            i = d.ident
            sec_rows.append([_tag(lvl, REPORT_LEVELS[lvl]), _e(display_name(d)), f"<code>{_e(d.mac)}</code>",
                             _e(f"{cat_meta(i.category)[1]} · {i.label}" if i.label else cat_meta(i.category)[1]),
                             (_e(f"{i.confidence}%" if i.confidence else "—"), i.confidence),
                             (_e(d.peak), d.peak), _e(_ts(d.first)),
                             f'<span class="muted">{_e("; ".join(clean(r, 80) for r in i.reasons[:4]))}</span>'])
        sec_html = _table(["Level", "Device", "MAC", "Category", "Conf.", "Peak dBm", "First seen", "Why"], sec_rows)
    else:
        sec_html = '<p class="muted">No security-relevant devices were flagged this session.</p>'

    tails = follow_rows()
    if tails:
        t_rows = []
        for t in tails:
            places = sum(1 for k, s_ in t.locs.items() if k >= 0 and s_ >= FOLLOW["min_loc_s"])
            tier = t.tier or "tracking"
            t_rows.append([(_tag("follower" if FOLLOW_RANK[t.tier] >= 2 else "info", tier.upper()), FOLLOW_RANK[t.tier]),
                           _e(t.label), f"<code>{_e(t.mac)}</code>", (_e(fmt_dur(t.near_s)), round(t.near_s)),
                           (_e(places), places), _e(_ts(t.first)), _e(_ts(t.last))])
        follow_html = _table(["Status", "Tracker", "MAC", "Close to you", "Places", "First", "Last near"], t_rows)
    else:
        follow_html = '<p class="muted">No trackers came close enough to be watched.</p>'

    ev = list(EVENTS)
    ev_html = ('<ul class="tl">' + "".join(
        f'<li><span class="muted">{_e(_ts(t))}</span>{_tag(l, l.upper())}<span>{_e(x)}</span></li>' for t, l, x in ev) + "</ul>"
        ) if ev else '<p class="muted">No notable events.</p>'

    if ghosts:
        g_rows = []
        for g in sorted(ghosts, key=lambda g: -g.rotations):
            first_dev = DEVICES.get(g.macs[0])
            label = clean((first_dev.ident.label or first_dev.name) if first_dev else (g.fp[0] if g.fp else ""), 40) or "unnamed"
            g_rows.append([f"<code>{_e(g.id)}</code>", _e(label), (_e(g.rotations), g.rotations), (_e(len(g.macs)), len(g.macs)),
                           _e(_ts(g.first)), _e(_ts(g.last))])
        ghost_html = _table(["Ghost ID", "Looks like", "Rotations", "MACs linked", "First", "Last"], g_rows)
    else:
        ghost_html = '<p class="muted">No address rotations were linked.</p>'

    d_rows = []
    for d in devs:
        i = d.ident
        d_ft = est_distance_ft(d.peak, d.tx)
        lvl = level_of.get(d.mac, "")
        d_rows.append([_e(display_name(d)), f"<code>{_e(d.mac)}</code>", _e(cat_meta(i.category)[1]),
                       _e(clean(i.vendor or i.label, 30)), f"<code>{_e(clean(adv_clues(d), 60))}</code>", _e(i.addr_type), _e(_ts(d.first)), _e(_ts(d.last)),
                       (_e(fmt_dur(d.last - d.first, True)), round(d.last - d.first)), (_e(f"{d.packets:,}"), d.packets),
                       (_e(d.peak), d.peak), ((">300" if d_ft > 300 else f"{d_ft:.0f}"), d_ft),
                       (_tag(lvl, REPORT_LEVELS[lvl]) if lvl else "", lvl)])
    dev_html = ('<input id="flt" type="search" placeholder="Filter devices…">' + _table(
        ["Device", "MAC", "Category", "Vendor / type", "Adv clues", "Address", "First", "Last", "Present", "Packets", "Peak dBm", "Closest ft", "Flag"],
        d_rows, tid="devtbl")) if d_rows else '<p class="muted">No devices were recorded.</p>'

    parts = [
        f"<h1>Signal OPS IRL — session report</h1><p class=\"sub\">{_e(_ts(start, True))} → {_e(_ts(end, True))} · passive BLE advertisement scan</p>",
        _section("Summary", cards),
        game_report_section(),
        _section("Security findings", sec_html),
        _section("Follower watch", follow_html),
        _section("Event timeline", ev_html),
        '<div class="grid2">' + _section("Category mix", _bars(cat_items)) + _section("Top vendors", _bars(ven_items)) + "</div>",
        '<div class="grid2">' + _section("Closest signal reached", _bars(sig_items)) + _section("Address types", _bars(addr_items)) + "</div>",
        _section("New devices over time", _bars(_arrival_items(devs, start, end))),
        _section("Rotating identities (MAC randomization)", ghost_html),
        _section(f"All devices seen ({len(devs)})", dev_html),
        _section("Session settings", meta),
        f"<footer>Generated {_e(_ts(end, True))} by Signal OPS IRL {_e(VERSION)}. Distances are rough RSSI estimates; "
        "ghost links and follower flags are probabilistic. Device names and addresses are broadcast by nearby radios and are shown as received.</footer>",
    ]
    csp = "default-src 'none'; style-src 'unsafe-inline'; script-src 'unsafe-inline'"
    return ("<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">"
            f"<meta http-equiv=\"Content-Security-Policy\" content=\"{csp}\">"
            "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"
            f"<title>Signal OPS IRL session {_e(_ts(start, True))}</title><style>{REPORT_CSS}</style></head>"
            f"<body><main>{''.join(parts)}</main><script>{REPORT_JS}</script></body></html>")

def write_session_report(report_dir=REPORT_DIR) -> Path:
    end = time.time()
    start = SESSION.get("start") or end
    doc = build_session_report(start, end)
    d = Path(report_dir)
    d.mkdir(parents=True, exist_ok=True)
    stem = datetime.datetime.fromtimestamp(start).strftime("signal_ops_%Y%m%d_%H%M%S")
    path, n = d / f"{stem}.html", 1
    while path.exists():
        path, n = d / f"{stem}_{n}.html", n + 1
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write(doc)
    return path

# =============================================================================
# CELEBRATION EFFECTS
# Large, centred full-screen animations for level-ups, quest completions, bounty claims, achievements and
# title unlocks. Each kind has its own look and its own sound file, looked up next to the script or in the
# current folder (any of .wav / .mp3 / .ogg / .flac):
#     level_up   quest_complete   bounty_claimed   achievement   title_unlock
# A missing file falls back to "notify", then to the terminal bell. Effects queue up if several fire at once.
# Press z to toggle the visuals (sounds keep playing), space to skip the current one, --test-fx to preview all.
# =============================================================================
FX_STYLES = {
    "level": {"headline": "LEVEL UP", "colors": ["bright_yellow", "yellow", "dark_orange", "bright_white"],
              "glyphs": "✦✧★▲", "motion": "rise", "duration": 5.0, "sound": "level_up"},
    "quest": {"headline": "QUEST COMPLETE", "colors": ["bright_green", "green", "spring_green2", "bright_white"],
              "glyphs": "✦✧•+", "motion": "fall", "duration": 3.8, "sound": "quest_complete"},
    "bounty": {"headline": "BOUNTY CLAIMED", "colors": ["gold1", "bright_yellow", "dark_orange", "bright_red"],
               "glyphs": "$¢◆●", "motion": "fall", "duration": 4.0, "sound": "bounty_claimed"},
    "achievement": {"headline": "ACHIEVEMENT", "colors": ["bright_cyan", "bright_magenta", "deep_sky_blue1", "bright_white"],
                    "glyphs": "✦✧★☆", "motion": "twinkle", "duration": 4.5, "sound": "achievement"},
    "title": {"headline": "TITLE UNLOCKED", "colors": ["medium_purple1", "hot_pink", "orchid1", "bright_white"],
              "glyphs": "✦✧♦◇", "motion": "rise", "duration": 4.2, "sound": "title_unlock"},
}
FX_STYLES["streak"] = {"headline": "STREAK MILESTONE", "colors": ["bright_red", "dark_orange", "bright_yellow", "bright_white"],
                       "glyphs": "✦▲♦•", "motion": "rise", "duration": 4.6, "sound": "streak_milestone"}
FX_STYLES["summary"] = {"headline": "MORE UNLOCKS", "colors": ["bright_white", "bright_cyan", "bright_yellow", "bright_magenta"],
                        "glyphs": "✦✧+•", "motion": "twinkle", "duration": 3.5, "sound": "achievement"}
FX_STYLES["shop"] = {"headline": "ITEM UNLOCKED", "colors": ["gold1", "bright_cyan", "bright_magenta", "bright_white"],
                     "glyphs": "¢$●◆", "motion": "fall", "duration": 4.0, "sound": "shop_unlock"}
FX_STYLES["mission"] = {"headline": "MISSION COMPLETE", "colors": ["bright_cyan", "cyan", "spring_green2", "bright_white"],
                        "glyphs": "✦◆▲•", "motion": "rise", "duration": 4.4, "sound": "mission_complete"}
FX_STYLES["mission_fail"] = {"headline": "MISSION FAILED", "colors": ["bright_red", "red", "dark_orange", "grey70"],
                             "glyphs": "✕▼•·", "motion": "fall", "duration": 3.2, "sound": "mission_failed"}
FX_STYLES["cache"] = {"headline": "CACHE OPENED", "colors": ["gold1", "bright_cyan", "bright_yellow", "bright_white"],
                      "glyphs": "◆▪$✦", "motion": "fall", "duration": 4.4, "sound": "cache_open"}
FX_PRIORITY = {"level": 5, "streak": 4, "title": 4, "achievement": 3, "mission": 3, "bounty": 2, "shop": 2, "cache": 2, "quest": 1, "mission_fail": 1, "summary": 0}
FX = {"queue": [], "cur": None, "hold_until": None, "dropped": 0}
FX_MAX_QUEUE = 10
FX_MAX_BURST = 3                 # most cards shown back to back; anything beyond is folded into one "more unlocks" card
FX_REVEAL = 0.45                 # seconds for the headline to wipe in
FX_FADE = 0.6                    # seconds of dimming at the end

# 5-row block font ('#' = filled, '.' = blank). Only used for the big headline and the level number.
_FX_SRC = {
    "A": "###/#.#/###/#.#/#.#", "B": "##./#.#/##./#.#/##.", "C": "###/#../#../#../###",
    "D": "##./#.#/#.#/#.#/##.", "E": "###/#../##./#../###", "F": "###/#../##./#../#..",
    "G": "###/#../#.#/#.#/###", "H": "#.#/#.#/###/#.#/#.#", "I": "###/.#./.#./.#./###",
    "J": "..#/..#/..#/#.#/###", "K": "#.#/#.#/##./#.#/#.#", "L": "#../#../#../#../###",
    "M": "#...#/##.##/#.#.#/#...#/#...#", "N": "#..#/##.#/#.##/#..#/#..#", "O": "###/#.#/#.#/#.#/###",
    "P": "###/#.#/###/#../#..", "Q": "###/#.#/#.#/###/..#", "R": "###/#.#/##./#.#/#.#",
    "S": "###/#../###/..#/###", "T": "###/.#./.#./.#./.#.", "U": "#.#/#.#/#.#/#.#/###",
    "V": "#.#/#.#/#.#/#.#/.#.", "W": "#...#/#...#/#.#.#/##.##/#...#", "X": "#.#/#.#/.#./#.#/#.#",
    "Y": "#.#/#.#/.#./.#./.#.", "Z": "###/..#/.#./#../###",
    "0": "###/#.#/#.#/#.#/###", "1": ".#./##./.#./.#./###", "2": "###/..#/###/#../###",
    "3": "###/..#/###/..#/###", "4": "#.#/#.#/###/..#/..#", "5": "###/#../###/..#/###",
    "6": "###/#../###/#.#/###", "7": "###/..#/..#/..#/..#", "8": "###/#.#/###/#.#/###",
    "9": "###/#.#/###/..#/###",
}
FX_FONT = {k: tuple(v.split("/")) for k, v in _FX_SRC.items()}
FX_FONT.update({
    " ": ("..",) * 5, "!": ("#", "#", "#", ".", "#"), ".": (".", ".", ".", ".", "#"), ":": (".", "#", ".", "#", "."),
    "-": ("...", "...", "###", "...", "..."), "+": ("...", ".#.", "###", ".#.", "..."),
})

def fx_big_rows(text: str, scale: int = 2) -> list:
    """Five strings of block characters spelling `text`. Each font pixel is `scale` cells wide."""
    glyphs = [FX_FONT[c] for c in text.upper() if c in FX_FONT]
    rows = []
    for r in range(5):
        parts = []
        for g in glyphs:
            w = max(len(x) for x in g)
            parts.append("".join("█" * scale if ch == "#" else " " * scale for ch in g[r].ljust(w, ".")))
        rows.append((" " * scale).join(parts))
    return rows

def fx_big(text: str, max_w: int, max_h: int):
    """Largest rendering of `text` that fits (wide, then wide stacked by word, then small, then small stacked).
    Returns a list of equal-width row strings, or None if nothing fits."""
    words = text.split()
    for scale in (2, 1):
        for stacked in (False, True):
            if stacked and len(words) < 2:
                continue
            blocks = words if stacked else [text]
            made = [fx_big_rows(b, scale) for b in blocks]
            if not all(any(r.strip() for r in rr) for rr in made):
                return None
            width = max(len(rr[0]) for rr in made)
            height = 5 * len(made) + (len(made) - 1)
            if width <= max_w and height <= max_h:
                out = []
                for i, rr in enumerate(made):
                    if i:
                        out.append(" " * width)
                    out += [r.center(width) for r in rr]
                return out
    return None

def game_fx(kind: str, name: str = "", detail: str = "", reward: str = "", big2: str = ""):
    """Queue a celebration. It starts (and its sound plays) as soon as nothing else is on screen."""
    if kind not in FX_STYLES:
        return
    if kind == "level":                                    # several level-ups in one burst: only the latest one is worth showing
        FX["queue"] = [f for f in FX["queue"] if f["kind"] != "level"]
    if len(FX["queue"]) >= FX_MAX_QUEUE:
        FX["queue"].pop(0)
        FX["dropped"] += 1
    FX["queue"].append(_fx_item(kind, name, detail, reward, big2))

def _fx_item(kind, name="", detail="", reward="", big2=""):
    return {"kind": kind, "name": clean(name, 60), "detail": clean(detail, 100), "reward": clean(reward, 40),
            "big2": str(big2 or ""), "seed": random.getrandbits(32), "start": None, "duration": 0.0}

def fx_collapse():
    """Too many waiting at once: keep the most important ones (in arrival order) and fold the rest into one summary card."""
    q = FX["queue"]
    extra = FX["dropped"]
    FX["dropped"] = 0
    burst = FX.get("max_burst", FX_MAX_BURST)
    if len(q) + (1 if extra else 0) <= burst:
        if extra:
            q.append(_fx_item("summary", "", f"{extra} more unlocked while you were busy", "Press p to see them all"))
        return
    keep_n = burst - 1
    ranked = sorted(range(len(q)), key=lambda i: (-FX_PRIORITY[q[i]["kind"]], i))[:keep_n]
    keep = [q[i] for i in sorted(ranked)]
    folded = len(q) - len(keep) + extra
    FX["queue"] = keep + [_fx_item("summary", "", f"{folded} more unlocked in a row", "Press p to see them all")]

def fx_tick(now: float):
    if FX["hold_until"] is None:                           # first tick of the session: let the startup flood settle first
        FX["hold_until"] = now + float(GCFG.get("settings", {}).get("notify_startup_delay", 30))
    cur = FX["cur"]
    if cur is not None and now - cur["start"] >= cur["duration"]:
        FX["cur"] = cur = None
    if cur is None and FX["queue"] and now >= FX["hold_until"] and not intro_playing():
        fx_collapse()
        cur = FX["queue"].pop(0)
        dur = FX_STYLES[cur["kind"]]["duration"] if CFG["fx"] else 1.2       # visuals off: just space the sounds out
        cur["start"], cur["duration"] = now, dur * (0.6 if FX["queue"] else 1.0)
        FX["cur"] = cur
        play_notification_sound(FX_STYLES[cur["kind"]]["sound"])

def fx_skip():
    FX["cur"] = None

def fx_active() -> bool:
    return bool(FX["cur"] and CFG["fx"])

def fx_visible(now: float):
    cur = FX["cur"]
    if cur and CFG["fx"] and cur["start"] is not None and now - cur["start"] < cur["duration"]:
        return cur
    return None

def fx_particles(fx, W: int, H: int, t: float) -> dict:
    """row -> [(x, glyph, colour)] for confetti that falls, sparks that rise, or stars that twinkle."""
    st = FX_STYLES[fx["kind"]]
    rng = random.Random(fx["seed"])
    rows = collections.defaultdict(list)
    for n in range(max(30, W * H // 40)):
        x, y0, speed = rng.randrange(W), rng.random() * H, rng.uniform(3.0, 9.0)
        g, col = rng.choice(st["glyphs"]), rng.choice(st["colors"])
        if st["motion"] == "twinkle":
            if (int(t * 4) + n) % 3 == 0:
                continue
            y = int(y0)
        else:
            y = int((y0 + (speed if st["motion"] == "fall" else -speed) * t) % H)
        rows[y].append((x, g, col))
    return rows

def fx_field(rows: dict, lo: int, hi: int, fading: bool, x0: int = 0, x1=None) -> Text:
    """Render particle rows lo..hi-1 for columns x0..x1-1 as one block of text."""
    out = Text(no_wrap=True, overflow="crop")
    for r in range(lo, hi):
        pos = x0
        for x, g, col in sorted(rows.get(r, ())):
            if x < pos or (x1 is not None and x >= x1):
                continue
            if x > pos:
                out.append(" " * (x - pos))
            out.append(g, style=f"dim {col}" if fading else col)
            pos = x + 1
        if r < hi - 1:
            out.append("\n")
    return out

def build_fx_screen(fx, size, now: float):
    """The whole screen: particles all around, a big animated panel in the middle. None if the terminal is too small."""
    W, H = size
    if W < 40 or H < 12:
        return None
    st = FX_STYLES[fx["kind"]]
    pal = st["colors"]
    t = max(0.0, now - fx["start"])
    fading = fx["duration"] - t < FX_FADE
    phase = int(t * 8)
    frac = min(1.0, t / FX_REVEAL)

    tails = [x for x in (fx["name"], fx["detail"], fx["reward"]) if x]
    head_max = (H - 4) - 2 - len(tails)                    # rows left for the headline (sparkle row + blank row reserved)
    inner_w = W - 12
    big2 = None
    if fx["big2"]:
        b2 = fx_big(fx["big2"], inner_w, 5)
        if b2 and head_max - 6 >= 5:
            big2, head_max = b2, head_max - 6
    head = fx_big(st["headline"], inner_w, head_max) or [st["headline"]]

    def paint(rows, offset):
        out = []
        for i, row in enumerate(rows):
            if not row.strip():
                out.append(Text(" " * len(row)))
                continue
            shown = row[: int(len(row) * frac)].ljust(len(row))      # left-to-right wipe-in
            out.append(Text(shown, style=("dim " if fading else "bold ") + pal[(i + phase + offset) % len(pal)], no_wrap=True))
        return out

    spark = Text(" ".join(st["glyphs"][(i + phase) % len(st["glyphs"])] for i in range(9)), style=pal[phase % len(pal)])
    lines = [spark] + paint(head, 0)
    if big2:
        lines += [Text("")] + paint(big2, 2)
    lines.append(Text(""))
    cw = max([len(r) for r in head + (big2 or [])] + [min(len(x), 70) for x in tails] + [20])
    pw = min(W - 2, max(44, cw + 10))
    for text, style in ((fx["name"], "bold bright_white"), (fx["detail"], "dim"), (fx["reward"], "bold yellow")):
        if text:
            lines.append(Text(text, style=style, no_wrap=True, overflow="ellipsis"))
    ph = len(lines) + 4

    border = "bold bright_white" if t < 0.25 else ("dim " + pal[0] if fading else pal[(phase // 2) % len(pal)])
    panel = Panel(Group(*[Align.center(x) for x in lines]), box=DOUBLE, border_style=border, width=pw, padding=(1, 2),
                  subtitle=Text("space: skip  ·  z: effects off", style="dim"))

    parts = fx_particles(fx, W, H, t)
    top_rows = max(0, (H - ph) // 2)
    bot_rows = max(0, H - ph - top_rows)
    lw = max(0, (W - pw) // 2)
    rw = W - lw - pw
    mid_cells = []
    if lw >= 2:
        mid_cells.append(Layout(fx_field(parts, top_rows, top_rows + ph, fading, 0, lw), size=lw))
    mid_cells.append(Layout(panel, size=pw))
    if rw >= 2:
        mid_cells.append(Layout(fx_field(parts, top_rows, top_rows + ph, fading, lw + pw, W), size=rw))
    mid = Layout(size=min(ph, H))
    mid.split_row(*mid_cells)

    rows_ = []
    if top_rows:
        rows_.append(Layout(fx_field(parts, 0, top_rows, fading), size=top_rows))
    rows_.append(mid)
    if bot_rows:
        rows_.append(Layout(fx_field(parts, top_rows + ph, H, fading), size=bot_rows))
    root = Layout()
    root.split_column(*rows_)
    return root

# =============================================================================
# GAME LAYER: XP / levels, daily quests, bounties, achievements, titles, profile
#
# All CONTENT (quests, bounties, achievements, titles, ranks, XP values, level curve) lives in
# lookout_game.json. Edit that file while the scanner runs: it is re-read automatically when it
# changes, and bad entries are skipped with a warning instead of breaking anything.
# Player progress is saved separately in lookout_profile.json.
# Run  python3 scanner.py --check-game  to validate the config and list every metric you can use.
# =============================================================================
GAME_CONFIG_FILE = "lookout_game.json"
PROFILE_FILE = "lookout_profile.json"

GAME_METRICS = {
    "devices_seen": "new devices that cleared your signal filter (a rotating address of a device already counted this session is not counted again)",
    "sessions": "scanner sessions started",
    "scan_minutes": "minutes spent actually scanning (paused time excluded)",
    "packets": "advertisement packets received",
    "alerts_found": "devices the scanner flagged ALERT",
    "possibles_found": "devices the scanner flagged POSSIBLE",
    "followers_flagged": "trackers that reached SUSPECT or ALERT in Follower Watch",
    "hunts_started": "hunts begun",
    "hunts_completed": "hunts finished by reaching the target",
    "rotations_linked": "private-address rotations linked back to one device (ghosts)",
    "devices_renamed": "devices you gave a permanent name",
    "quests_completed": "daily quests completed",
    "bounties_claimed": "bounties claimed",
    "max_in_range": "most devices in range at once (gauge)",
    "distinct_categories": "different device categories seen (gauge)",
    "distinct_vendors": "different vendors seen (gauge)",
    "streak_days": "current daily streak (gauge, lifetime only)",
    "longest_session_minutes": "longest single scan session in minutes (lifetime only)",
    "level": "current level (lifetime only)",
    "total_xp": "total XP earned (lifetime only)",
    "achievements_unlocked": "achievements unlocked (lifetime only)",
    "missions_started": "timed missions started (press y)",
    "missions_completed": "timed missions finished in time",
    "missions_failed": "timed missions that ran out of clock",
    "active_days": "days you scanned long enough to count toward the streak (total, not consecutive)",
    "caches_opened": "daily caches and weekly chests opened",
    "weekly_goals_done": "weekly ops completed",
    "shields_used": "missed days a Streak Shield covered",
}
GAME_METRIC_PREFIXES = {
    "category:": "new devices seen in a category, e.g. category:trackers_valuables",
    "tier:": "new devices by identification tier, e.g. tier:alert or tier:possible",
    "vendor:": "new devices by vendor name (lowercase), e.g. vendor:apple, inc. (exact lowercase vendor name)",
    "addr:": "new devices by address type, e.g. addr:public",
}
GAME_XP_EVENTS = {
    "new_device": "each new device", "new_category": "first time ever seeing a category",
    "new_vendor": "first time ever seeing a vendor", "alert_device": "each ALERT-flagged device",
    "possible_device": "each POSSIBLE-flagged device", "follower_alert": "each tracker that becomes SUSPECT/ALERT",
    "hunt_completed": "each finished hunt", "rotation_linked": "each linked address rotation",
    "scan_minute": "each full minute of scanning", "daily_login": "first session of each day",
}
# ---- Intel Coins: defaults (all of it can be overridden in lookout_game.json) ----
COIN_ICON = "🪙"
GAME_DEFAULT_COIN_RULES = {"new_category": 3, "alert_device": 4, "possible_device": 2, "follower_alert": 5, "hunt_completed": 4,
                           "daily_login": 2, "level_up": 5, "all_quests_done": 10, "device_batch": 1, "scan_hour": 2,
                           "bounty_easy": 5, "bounty_medium": 10, "bounty_hard": 20, "bounty_elite": 40,
                           "mission_easy": 5, "mission_medium": 10, "mission_hard": 20, "mission_elite": 40, "mission_speed_bonus": 3}
GAME_DEFAULT_COIN_CAPS = {"alert_device": 20, "possible_device": 20, "follower_alert": 25, "hunt_completed": 20,
                          "device_batch": 20, "scan_hour": 24, "mission_reward": 80}
GAME_COIN_EVENTS = {
    "new_category": "first time ever seeing a category", "alert_device": "each ALERT-flagged device",
    "possible_device": "each POSSIBLE-flagged device", "follower_alert": "each tracker that becomes SUSPECT/ALERT",
    "hunt_completed": "each finished hunt", "daily_login": "first session of each day", "level_up": "each level gained",
    "all_quests_done": "finishing every daily quest in a day", "device_batch": "every batch of new devices (settings.devices_per_coin)",
    "scan_hour": "each full hour of scanning", "bounty_easy": "claiming an EASY bounty", "bounty_medium": "claiming a MEDIUM bounty",
    "bounty_hard": "claiming a HARD bounty", "bounty_elite": "claiming an ELITE bounty",
    "mission_easy": "completing an EASY mission", "mission_medium": "completing a MEDIUM mission",
    "mission_hard": "completing a HARD mission", "mission_elite": "completing an ELITE mission",
    "mission_speed_bonus": "finishing a mission with at least half the clock left",
    "mission_reward": "all mission coins together (a daily cap only: set coin_caps.mission_reward)",
}
SHOP_TYPES = {"theme": "Interface theme", "neon": "Visual mode", "glitch": "Glitch effect", "decrypt": "Terminal extra",
              "boost": "Consumable"}
THEME_MODES = ("mono", "duo", "cycle")
GLITCH_KINDS = ("tear", "split", "corrupt", "flash")
SHOP_DEFAULT = [
    {"id": "theme-matrix", "type": "theme", "name": "Matrix", "description": "Green phosphor on black. The classic.",
     "price": 80, "spec": {"mode": "mono", "colors": ["#00ff41"]}},
    {"id": "theme-amber", "type": "theme", "name": "Amber CRT", "description": "Warm amber monochrome, like a 1980s terminal.",
     "price": 80, "spec": {"mode": "mono", "colors": ["#ffb000"]}},
    {"id": "theme-ice", "type": "theme", "name": "Cyber Ice", "description": "Cold blue-white monochrome.",
     "price": 110, "spec": {"mode": "mono", "colors": ["#5ad1ff"]}},
    {"id": "theme-phantom", "type": "theme", "name": "Phantom", "description": "Violet monochrome for night operations.",
     "price": 110, "spec": {"mode": "mono", "colors": ["#b388ff"]}},
    {"id": "theme-toxic", "type": "theme", "name": "Toxic Waste", "description": "Acid green and ultraviolet two-tone.",
     "price": 160, "min_level": 3, "spec": {"mode": "duo", "colors": ["#b6ff00", "#9d4dff"]}},
    {"id": "theme-synthwave", "type": "theme", "name": "Synthwave", "description": "Hot magenta and electric cyan two-tone.",
     "price": 160, "min_level": 3, "spec": {"mode": "duo", "colors": ["#ff2bd6", "#00e5ff", "#ffd6f7"]}},
    {"id": "theme-prism", "type": "theme", "name": "Prism", "description": "Keeps every colour but slowly cycles the whole spectrum.",
     "price": 300, "min_level": 10, "spec": {"mode": "cycle", "colors": []}},
    {"id": "neon-mode", "type": "neon", "name": "Neon Mode",
     "description": "Colours glow and breathe; panel borders become light tubes with a colour wave running along them. Stacks with any theme.",
     "price": 250, "min_level": 5},
    {"id": "glitch-tear", "type": "glitch", "name": "Signal Tear", "description": "Rows of the screen occasionally slip sideways, like a bad signal.",
     "price": 150, "spec": {"kinds": ["tear"], "level": 1}},
    {"id": "glitch-chroma", "type": "glitch", "name": "Chroma Split", "description": "Brief flashes of cyan / magenta colour splitting across rows.",
     "price": 200, "min_level": 2, "spec": {"kinds": ["split"], "level": 2}},
    {"id": "glitch-corrupt", "type": "glitch", "name": "Data Corruption", "description": "Text garbles into block noise for a moment, then recovers.",
     "price": 200, "min_level": 2, "spec": {"kinds": ["corrupt"], "level": 2}},
    {"id": "glitch-meltdown", "type": "glitch", "name": "Total Meltdown", "description": "Tearing, colour splits, corruption and polarity flashes, all at once and often.",
     "price": 500, "min_level": 15, "spec": {"kinds": ["tear", "split", "corrupt", "flash"], "level": 3}},
    {"id": "decrypt-status", "type": "decrypt", "name": "Decrypt Status Line", "description": "Status messages scramble, then decode left to right.",
     "price": 120},
    {"id": "streak-shield", "type": "boost", "name": "Streak Shield",
     "description": "Covers one missed day so your streak survives. Used automatically. Buy more any time (you can hold a few).",
     "price": 150},
]
GAME_DEFAULT_SETTINGS = {"daily_quest_count": 3, "day_rollover_hour": 0, "level_cap": 100, "level_base_xp": 100,
                         "level_growth": 1.07, "level_xp_multiplier": 4.0,
                         "achievement_target_multiplier": 3.0, "bounty_count_multiplier": 3.0, "notify_startup_delay": 30, "streak_min_scan_minutes": 5, "streak_bonus_xp": 10, "streak_bonus_cap": 7,
                         "quest_xp_per_coin": 15, "achievement_xp_per_coin": 20, "streak_xp_per_coin": 30, "devices_per_coin": 50,
                         "coin_icon": COIN_ICON}
GAME_DEFAULT_XP = {"new_device": 1, "new_category": 25, "new_vendor": 5, "alert_device": 40, "possible_device": 15,
                   "follower_alert": 50, "hunt_completed": 60, "rotation_linked": 3, "scan_minute": 1, "daily_login": 15}
GAME_DEFAULT_CAPS = {"follower_alert": 150, "hunt_completed": 300, "rotation_linked": 60, "scan_minute": 180}
BOUNTY_DIFF = {"easy": ("EASY", "green"), "medium": ("MEDIUM", "yellow"), "hard": ("HARD", "red"), "elite": ("ELITE", "magenta")}
GAME_PAGES = ["Profile", "Daily quests", "Weekly ops", "Bounties", "Achievements", "Titles", "Intel Coins", "Shop"]
TITLE_TYPES = ("always", "level", "achievement", "bounty", "quest", "metric")

GAME = {"on": False, "cfg_path": GAME_CONFIG_FILE, "profile_path": PROFILE_FILE, "mtime": 0.0, "last_check": 0.0,
        "last_save": 0.0, "last_eval": 0.0, "dirty": False, "pending": [], "warnings": [], "credited": set(),
        "scan_acc": 0.0, "session_scan_s": 0.0, "last_packets": 0, "session_xp": 0, "session_start_level": 1,
        "session_log": [], "level_xp": [0], "qmap": {}, "bmap": {}, "amap": {}, "tmap": {}, "vset": set(), "cset": set(),
        "player_arg": None, "cfg_error": "", "session_coins": 0, "scan_min_n": 0, "smap": {}, "mimap": {}}
GCFG: dict = {}
STATE: dict = {}
GAME_UI = {"page": 0, "scroll": 0}

# ---------------------------------------------------------------- config parsing
def _gnum(v, default, lo=None, hi=None):
    try:
        x = float(v)
    except (TypeError, ValueError):
        return default
    if x != x or x in (float("inf"), float("-inf")):
        return default
    if lo is not None:
        x = max(lo, x)
    if hi is not None:
        x = min(hi, x)
    return x

def _glist(v) -> list:
    return v if isinstance(v, list) else []

def _gid(raw, kind, seen, warns):
    s = str(raw or "").strip().lower()
    if not re.fullmatch(r"[a-z0-9][a-z0-9_\-]{0,47}", s):
        warns.append(f"{kind}: bad or missing id {raw!r} (use a-z 0-9 _ - , max 48 chars); skipped")
        return None
    if s in seen:
        warns.append(f"{kind} '{s}': duplicate id; skipped")
        return None
    seen.add(s)
    return s

def game_metric_known(name: str) -> bool:
    return name in GAME_METRICS or any(name.startswith(p) and len(name) > len(p) for p in GAME_METRIC_PREFIXES)

def compile_match(m, label: str, warns: list):
    """Turn a bounty 'match' block into a rule dict. Returns None (with a warning) if unusable."""
    if not isinstance(m, dict) or not m:
        warns.append(f"{label}: needs a non-empty 'match' object; skipped")
        return None
    rule = {}
    lst = lambda v: v if isinstance(v, list) else [v]
    for k, v in m.items():
        if k in ("category", "tier", "addr_type"):
            rule[k] = {str(x).strip().lower() for x in lst(v)}
        elif k in ("vendor", "name", "label"):
            try:
                rule[k] = re.compile(str(v)[:200], re.I)
            except re.error as e:
                warns.append(f"{label}: bad regex in match.{k} ({e}); skipped")
                return None
        elif k == "uuid":
            rule[k] = {str(x).strip().upper().removeprefix("0X") for x in lst(v)}
        elif k == "mfg":
            ids = set()
            for x in lst(v):
                try:
                    ids.add(int(str(x), 0))
                except ValueError:
                    warns.append(f"{label}: match.mfg value {x!r} is not a number (use 76 or \"0x004C\")")
            if not ids:
                return None
            rule[k] = ids
        elif k == "min_rssi":
            rule[k] = _gnum(v, -100.0, -127, 0)
        elif k == "followed":
            rule[k] = bool(v)
        else:
            warns.append(f"{label}: unknown match key '{k}' ignored")
    if not rule:
        warns.append(f"{label}: no usable match conditions; skipped")
        return None
    return rule

def _scaled_bounty_count(count: int, mult: float) -> int:
    """Multi-find bounties need `mult` times as many matches; single-find bounties stay single (they're gated by rarity)."""
    return count if count <= 1 else min(2000, max(2, round(count * mult)))

def _shop_spec(typ: str, spec, label: str, warns: list):
    """Validate a shop item's effect parameters. Returns the cleaned spec, or None (with a warning) if unusable."""
    spec = spec if isinstance(spec, dict) else {}
    if typ == "theme":
        mode = str(spec.get("mode", "mono")).lower()
        if mode not in THEME_MODES:
            warns.append(f"{label}: spec.mode must be one of {', '.join(THEME_MODES)}; skipped")
            return None
        cols = []
        for x in _glist(spec.get("colors")):
            rgb = parse_hex_color(x)
            if rgb is None:
                warns.append(f"{label}: colour {x!r} is not #rrggbb; skipped")
                return None
            cols.append(rgb)
        if mode != "cycle" and not cols:
            warns.append(f"{label}: a {mode} theme needs spec.colors (#rrggbb)" + ("" if mode == "mono" else ", two or three of them") + "; skipped")
            return None
        if mode == "duo" and len(cols) < 2:
            warns.append(f"{label}: a duo theme needs at least two colours; skipped")
            return None
        return {"mode": mode, "colors": cols[:3]}
    if typ == "glitch":
        kinds = [str(k).lower() for k in _glist(spec.get("kinds"))]
        bad = [k for k in kinds if k not in GLITCH_KINDS]
        if bad or not kinds:
            warns.append(f"{label}: spec.kinds must be a list from {', '.join(GLITCH_KINDS)}" + (f" (got {bad})" if bad else "") + "; skipped")
            return None
        return {"kinds": kinds, "level": int(_gnum(spec.get("level"), 2, 1, 3))}
    return {}

def parse_shop(raw, warns: list) -> list:
    """The shop catalog: built-in items, overridden / extended by the config's 'shop' list.
    A config entry with a known id changes that item (name, description, price, min_level, hidden, enabled, and theme/glitch spec);
    a new id adds an item (type 'theme' or 'glitch' only: neon and decrypt are single built-in effects)."""
    items: dict = {}
    for d in SHOP_DEFAULT:
        spec = _shop_spec(d["type"], d.get("spec"), f"shop '{d['id']}'", [])
        items[d["id"]] = {"id": d["id"], "type": d["type"], "name": d["name"], "desc": d["description"], "price": d["price"],
                          "min_level": d.get("min_level", 1), "hidden": False, "spec": spec}
    seen = set()
    for e in _glist(raw):
        if not isinstance(e, dict):
            warns.append("shop: entry is not an object; skipped")
            continue
        iid = _gid(e.get("id"), "shop item", seen, warns)
        if not iid:
            continue
        cur = items.get(iid)
        if cur is None:
            typ = str(e.get("type", "")).lower()
            if typ not in ("theme", "glitch"):
                warns.append(f"shop item '{iid}': new items need type 'theme' or 'glitch'; skipped")
                continue
            spec = _shop_spec(typ, e.get("spec"), f"shop item '{iid}'", warns)
            if spec is None:
                continue
            cur = items[iid] = {"id": iid, "type": typ, "name": iid, "desc": "", "price": 100, "min_level": 1, "hidden": False, "spec": spec}
        elif "spec" in e and cur["type"] in ("theme", "glitch"):
            spec = _shop_spec(cur["type"], e.get("spec"), f"shop item '{iid}'", warns)
            if spec is not None:
                cur["spec"] = spec
        if e.get("enabled") is False:
            items.pop(iid, None)
            continue
        if "name" in e:
            cur["name"] = clean(e["name"], 32) or cur["name"]
        if "description" in e:
            cur["desc"] = clean(e["description"], 140)
        if "price" in e:
            cur["price"] = int(_gnum(e["price"], cur["price"], 1, 1e7))
        if "min_level" in e:
            cur["min_level"] = int(_gnum(e["min_level"], cur["min_level"], 1, 1000))
        if "hidden" in e:
            cur["hidden"] = bool(e["hidden"])
    return list(items.values())

def _opt_coins(raw):
    """Optional per-entry 'coins' override on a quest / bounty / achievement (None = use the config's rates)."""
    v = raw.get("coins")
    return None if v is None else int(_gnum(v, 0, 0, 1e5))

# ---------------------------------------------------------------- daily hooks (the "retention" block of the game config)
# Reasons to come back every day: a Daily Surge (bonus XP in your first minutes of the day), Streak Shields (a missed day
# doesn't wipe a streak), a coin ladder that grows with the streak, Daily Caches (loot boxes for finishing quests), Weekly Ops
# (bigger goals that reset every Monday, with a Weekly Chest) and a Welcome Back bonus. Everything is optional and editable.
RET_GAUGES = frozenset({"max_in_range", "distinct_categories", "distinct_vendors", "streak_days", "longest_session_minutes",
                        "level", "total_xp", "achievements_unlocked"})
RETENTION_DEFAULT = {
    "surge": {"enabled": True, "minutes": 15, "multiplier": 2.0},
    "streak_ladder": [2, 2, 3, 3, 4, 5, 10],
    "shield": {"max": 2, "free_every": 7},
    "comeback": {"min_days_away": 3, "xp": 100, "coins": 10},
    "caches": [
        {"id": "bronze", "name": "Bronze Cache", "quests": 3, "coins": [3, 8], "xp": [20, 50],
         "shield_chance": 0.0, "jackpot_chance": 0.03, "jackpot_mult": 4.0},
        {"id": "silver", "name": "Silver Cache", "quests": 6, "coins": [6, 14], "xp": [40, 100],
         "shield_chance": 0.10, "jackpot_chance": 0.05, "jackpot_mult": 4.0},
        {"id": "gold", "name": "Gold Cache", "quests": "all", "coins": [12, 30], "xp": [80, 200],
         "shield_chance": 0.25, "jackpot_chance": 0.08, "jackpot_mult": 5.0},
    ],
    "weekly_count": 4,
    "weekly": [
        {"id": "week-show-up", "name": "Show Up", "desc": "Scan on 5 different days this week.", "metric": "active_days", "target": 5,
         "xp": 250, "coins": None, "min_level": 1, "always": True},
        {"id": "week-devices", "name": "Wide Net", "desc": "Discover 400 new devices this week.", "metric": "devices_seen", "target": 400,
         "xp": 200, "coins": None, "min_level": 1, "always": False},
        {"id": "week-scan", "name": "Long Watch", "desc": "Scan for 3 hours in total this week.", "metric": "scan_minutes", "target": 180,
         "xp": 200, "coins": None, "min_level": 1, "always": False},
        {"id": "week-quests", "name": "Quest Grinder", "desc": "Finish 15 daily quests this week.", "metric": "quests_completed", "target": 15,
         "xp": 250, "coins": None, "min_level": 1, "always": False},
        {"id": "week-bounties", "name": "Bounty Run", "desc": "Claim 3 bounties this week.", "metric": "bounties_claimed", "target": 3,
         "xp": 250, "coins": None, "min_level": 1, "always": False},
        {"id": "week-missions", "name": "Mission Runner", "desc": "Complete 3 timed missions this week.", "metric": "missions_completed", "target": 3,
         "xp": 200, "coins": None, "min_level": 1, "always": False},
    ],
    "weekly_chest": {"enabled": True, "name": "Weekly Chest", "coins": [40, 90], "xp": [300, 700],
                     "shield_chance": 1.0, "jackpot_chance": 0.10, "jackpot_mult": 3.0},
}
RET_CACHE_BASE = {"name": "Cache", "coins": [3, 8], "xp": [20, 50], "shield_chance": 0.0, "jackpot_chance": 0.0, "jackpot_mult": 3.0}

def _ret_pair(v, default, lo, hi) -> list:
    if isinstance(v, (list, tuple)) and len(v) == 2:
        a, b = int(_gnum(v[0], default[0], lo, hi)), int(_gnum(v[1], default[1], lo, hi))
        return [min(a, b), max(a, b)]
    if isinstance(v, (int, float)) and not isinstance(v, bool):
        a = int(_gnum(v, default[0], lo, hi))
        return [a, a]
    return list(default)

def _ret_reward(raw: dict, base: dict) -> dict:
    """The loot-table fields shared by daily caches and the weekly chest."""
    out = dict(base)
    out["name"] = clean(raw.get("name") or base.get("name") or "Cache", 32)
    out["coins"] = _ret_pair(raw.get("coins"), base["coins"], 0, 100000)
    out["xp"] = _ret_pair(raw.get("xp"), base["xp"], 0, 1000000)
    out["shield_chance"] = _gnum(raw.get("shield_chance"), base["shield_chance"], 0.0, 1.0)
    out["jackpot_chance"] = _gnum(raw.get("jackpot_chance"), base["jackpot_chance"], 0.0, 1.0)
    out["jackpot_mult"] = _gnum(raw.get("jackpot_mult"), base["jackpot_mult"], 1.0, 50.0)
    return out

def parse_retention(raw, warns: list) -> dict:
    """Validate the optional 'retention' block. Never raises; missing or bad parts fall back to the built-in defaults."""
    r = json.loads(json.dumps(RETENTION_DEFAULT))
    if raw is None:
        return r
    if not isinstance(raw, dict):
        warns.append("retention: must be an object; using the built-in daily hooks")
        return r
    sg = raw.get("surge")
    if isinstance(sg, dict):
        s = r["surge"]
        s["enabled"] = bool(sg.get("enabled", s["enabled"]))
        s["minutes"] = _gnum(sg.get("minutes"), s["minutes"], 1, 600)
        s["multiplier"] = _gnum(sg.get("multiplier"), s["multiplier"], 1.0, 10.0)
    lad = raw.get("streak_ladder")
    if isinstance(lad, list) and lad:
        r["streak_ladder"] = [int(_gnum(x, 0, 0, 10000)) for x in lad[:31]]
    elif lad is not None:
        warns.append("retention.streak_ladder: must be a list of coin amounts (one per streak day, repeating); using the default")
    sh = raw.get("shield")
    if isinstance(sh, dict):
        r["shield"]["max"] = int(_gnum(sh.get("max"), r["shield"]["max"], 0, 10))
        r["shield"]["free_every"] = int(_gnum(sh.get("free_every"), r["shield"]["free_every"], 0, 365))
    cb = raw.get("comeback")
    if isinstance(cb, dict):
        c = r["comeback"]
        c["min_days_away"] = int(_gnum(cb.get("min_days_away"), c["min_days_away"], 0, 365))
        c["xp"] = int(_gnum(cb.get("xp"), c["xp"], 0, 1e5))
        c["coins"] = int(_gnum(cb.get("coins"), c["coins"], 0, 1e4))
    if "caches" in raw:
        lst = raw["caches"]
        if isinstance(lst, list):
            seen, out = set(), []
            for e in lst:
                if not isinstance(e, dict):
                    warns.append("retention.caches: entry is not an object; skipped"); continue
                cid = _gid(e.get("id"), "cache", seen, warns)
                if not cid:
                    continue
                q = e.get("quests", "all")
                if isinstance(q, str) and q.strip().lower() == "all":
                    need = "all"
                else:
                    need = int(_gnum(q, 0, 0, 10))
                    if need <= 0:
                        warns.append(f"cache '{cid}': 'quests' must be 1 to 10 or \"all\"; skipped"); continue
                c = _ret_reward(e, RET_CACHE_BASE)
                c["id"], c["quests"] = cid, need
                out.append(c)
            out.sort(key=lambda c: 99 if c["quests"] == "all" else c["quests"])
            r["caches"] = out
        else:
            warns.append("retention.caches: must be a list; using the default caches")
    wc = raw.get("weekly_chest")
    if isinstance(wc, dict):
        r["weekly_chest"] = _ret_reward(wc, r["weekly_chest"])
        r["weekly_chest"]["enabled"] = bool(wc.get("enabled", True))
    r["weekly_count"] = int(_gnum(raw.get("weekly_count"), r["weekly_count"], 0, 8))
    if "weekly" in raw:
        lst = raw["weekly"]
        if isinstance(lst, list):
            seen, goals = set(), []
            for e in lst:
                if not isinstance(e, dict):
                    warns.append("retention.weekly: entry is not an object; skipped"); continue
                gid = _gid(e.get("id"), "weekly goal", seen, warns)
                if not gid:
                    continue
                metric = str(e.get("metric", "")).strip().lower()
                target = _gnum(e.get("target"), 0, 0)
                if target <= 0:
                    warns.append(f"weekly goal '{gid}': 'target' must be a number above 0; skipped"); continue
                if not game_metric_known(metric) or metric in RET_GAUGES:
                    warns.append(f"weekly goal '{gid}': '{metric}' is not a counter metric (gauges like level or streak_days can't be tracked weekly); skipped"); continue
                goals.append({"id": gid, "name": clean(e.get("name") or gid, 40), "desc": clean(e.get("description", ""), 120),
                              "metric": metric, "target": target, "xp": int(_gnum(e.get("xp"), 150, 0, 1e6)), "coins": _opt_coins(e),
                              "min_level": int(_gnum(e.get("min_level"), 1, 1, 1000)), "always": bool(e.get("always"))})
            r["weekly"] = goals
        else:
            warns.append("retention.weekly: must be a list; using the default weekly goals")
    return r

def parse_game_config(data):
    """Validate the JSON. Never raises: returns (config, warnings). Bad entries are skipped."""
    warns = []
    cfg = {"settings": dict(GAME_DEFAULT_SETTINGS), "xp_rules": dict(GAME_DEFAULT_XP), "xp_caps": dict(GAME_DEFAULT_CAPS),
           "ranks": [], "quests": [], "bounties": [], "achievements": [], "titles": [],
           "coin_rules": dict(GAME_DEFAULT_COIN_RULES), "coin_caps": dict(GAME_DEFAULT_COIN_CAPS), "shop": parse_shop(None, []),
           "missions": [], "boot": dict(GAME_DEFAULT_BOOT), "retention": parse_retention(None, [])}
    if not isinstance(data, dict):
        return cfg, ["config root must be a JSON object"]
    st, s = data.get("settings"), cfg["settings"]
    if isinstance(st, dict):
        if _gnum(st.get("daily_quest_count"), 0) > 10:
            warns.append(f"settings.daily_quest_count: {st.get('daily_quest_count')} is above the maximum of 10; using 10")
        s["daily_quest_count"] = int(_gnum(st.get("daily_quest_count"), s["daily_quest_count"], 0, 10))
        s["day_rollover_hour"] = int(_gnum(st.get("day_rollover_hour"), s["day_rollover_hour"], 0, 23))
        s["level_cap"] = int(_gnum(st.get("level_cap"), s["level_cap"], 2, 200))
        s["level_base_xp"] = _gnum(st.get("level_base_xp"), s["level_base_xp"], 1, 1e6)
        s["level_growth"] = _gnum(st.get("level_growth"), s["level_growth"], 1.0, 1.5)
        s["level_xp_multiplier"] = _gnum(st.get("level_xp_multiplier"), s["level_xp_multiplier"], 0.1, 1000)
        s["achievement_target_multiplier"] = _gnum(st.get("achievement_target_multiplier"), s["achievement_target_multiplier"], 0.1, 1000)
        s["bounty_count_multiplier"] = _gnum(st.get("bounty_count_multiplier"), s["bounty_count_multiplier"], 0.1, 1000)
        s["notify_startup_delay"] = _gnum(st.get("notify_startup_delay"), s["notify_startup_delay"], 0, 600)
        s["streak_min_scan_minutes"] = _gnum(st.get("streak_min_scan_minutes"), s["streak_min_scan_minutes"], 0, 1440)
        s["streak_bonus_xp"] = int(_gnum(st.get("streak_bonus_xp"), s["streak_bonus_xp"], 0, 1e5))
        s["streak_bonus_cap"] = int(_gnum(st.get("streak_bonus_cap"), s["streak_bonus_cap"], 1, 365))
        s["quest_xp_per_coin"] = _gnum(st.get("quest_xp_per_coin"), s["quest_xp_per_coin"], 0.1, 1e6)
        s["achievement_xp_per_coin"] = _gnum(st.get("achievement_xp_per_coin"), s["achievement_xp_per_coin"], 0.1, 1e6)
        s["streak_xp_per_coin"] = _gnum(st.get("streak_xp_per_coin"), s["streak_xp_per_coin"], 0.1, 1e6)
        s["devices_per_coin"] = _gnum(st.get("devices_per_coin"), s["devices_per_coin"], 0, 1e6)
        s["coin_icon"] = clean(st.get("coin_icon", s["coin_icon"]), 4) or COIN_ICON
    for key, dest in (("xp_rules", cfg["xp_rules"]), ("xp_caps", cfg["xp_caps"]),
                      ("coin_rules", cfg["coin_rules"]), ("coin_caps", cfg["coin_caps"])):
        events = GAME_COIN_EVENTS if key.startswith("coin") else GAME_XP_EVENTS
        block = data.get(key)
        if isinstance(block, dict):
            for k, v in block.items():
                if k not in events:
                    warns.append(f"{key}.{k}: not a known {'coin' if key.startswith('coin') else 'XP'} event (known: {', '.join(events)}); ignored")
                elif v is None and key.endswith("_caps"):
                    dest.pop(k, None)                              # null removes the daily cap
                else:
                    dest[k] = int(_gnum(v, dest.get(k, 0), 0, 1e6))
    for r in _glist(data.get("ranks")):
        if isinstance(r, dict) and r.get("name"):
            cfg["ranks"].append((int(_gnum(r.get("level"), 1, 1, 1000)), clean(r["name"], 30)))
    cfg["ranks"].sort()

    seen = set()
    for raw in _glist(data.get("quests")):
        if not isinstance(raw, dict):
            warns.append("quests: entry is not an object; skipped"); continue
        qid = _gid(raw.get("id"), "quest", seen, warns)
        if not qid:
            continue
        metric = str(raw.get("metric", "")).strip().lower()
        target = _gnum(raw.get("target"), 0, 0)
        if target <= 0:
            warns.append(f"quest '{qid}': 'target' must be a number above 0; skipped"); continue
        if not game_metric_known(metric):
            warns.append(f"quest '{qid}': unknown metric '{metric}' (it can never progress)")
        cfg["quests"].append({"id": qid, "name": clean(raw.get("name") or qid, 48), "desc": clean(raw.get("description", ""), 140),
                              "metric": metric, "target": target, "xp": int(_gnum(raw.get("xp"), 0, 0, 1e6)),
                              "min_level": int(_gnum(raw.get("min_level"), 1, 1, 1000)), "weight": _gnum(raw.get("weight"), 1, 0.01, 100),
                              "coins": _opt_coins(raw)})
    seen = set()
    for raw in _glist(data.get("bounties")):
        if not isinstance(raw, dict):
            warns.append("bounties: entry is not an object; skipped"); continue
        bid = _gid(raw.get("id"), "bounty", seen, warns)
        if not bid:
            continue
        rule = compile_match(raw.get("match"), f"bounty '{bid}'", warns)
        if rule is None:
            continue
        diff = str(raw.get("difficulty", "medium")).lower()
        rep = str(raw.get("repeat", "once")).lower()
        if diff not in BOUNTY_DIFF:
            warns.append(f"bounty '{bid}': difficulty '{diff}' unknown (easy/medium/hard/elite); using medium"); diff = "medium"
        if rep not in ("once", "daily"):
            warns.append(f"bounty '{bid}': repeat '{rep}' unknown (once/daily); using once"); rep = "once"
        cfg["bounties"].append({"id": bid, "name": clean(raw.get("name") or bid, 48), "desc": clean(raw.get("description", ""), 140),
                                "xp": int(_gnum(raw.get("xp"), 0, 0, 1e6)), "difficulty": diff, "repeat": rep,
                                "count": _scaled_bounty_count(int(_gnum(raw.get("count"), 1, 1, 500)), s["bounty_count_multiplier"]),
                                "match": rule, "coins": _opt_coins(raw)})
    seen = set()
    for raw in _glist(data.get("achievements")):
        if not isinstance(raw, dict):
            warns.append("achievements: entry is not an object; skipped"); continue
        aid = _gid(raw.get("id"), "achievement", seen, warns)
        if not aid:
            continue
        metric = str(raw.get("metric", "")).strip().lower()
        target = _gnum(raw.get("target"), 0, 0)
        if target <= 0:
            warns.append(f"achievement '{aid}': 'target' must be a number above 0; skipped"); continue
        if not game_metric_known(metric):
            warns.append(f"achievement '{aid}': unknown metric '{metric}' (it can never unlock)")
        cfg["achievements"].append({"id": aid, "name": clean(raw.get("name") or aid, 48), "desc": clean(raw.get("description", ""), 140),
                                    "metric": metric, "target": max(1.0, float(round(target * s["achievement_target_multiplier"]))),
                                    "xp": int(_gnum(raw.get("xp"), 0, 0, 1e6)),
                                    "hidden": bool(raw.get("hidden", False)), "icon": clean(raw.get("icon", "🏆"), 4) or "🏆",
                                    "coins": _opt_coins(raw)})
    seen = set()
    for raw in _glist(data.get("titles")):
        if not isinstance(raw, dict):
            warns.append("titles: entry is not an object; skipped"); continue
        tid = _gid(raw.get("id"), "title", seen, warns)
        if not tid:
            continue
        un = raw.get("unlock", {"type": "always"})
        typ = str(un.get("type", "")).lower() if isinstance(un, dict) else ""
        if typ not in TITLE_TYPES:
            warns.append(f"title '{tid}': unlock.type must be one of {', '.join(TITLE_TYPES)}; skipped"); continue
        u = {"type": typ}
        if typ == "level":
            u["value"] = int(_gnum(un.get("value"), 1, 1, 1000))
        elif typ in ("achievement", "bounty", "quest"):
            u["id"] = str(un.get("id", "")).strip().lower()
        elif typ == "metric":
            u["metric"] = str(un.get("metric", "")).strip().lower()
            u["target"] = _gnum(un.get("target"), 0, 0)
            if u["target"] <= 0 or not game_metric_known(u["metric"]):
                warns.append(f"title '{tid}': needs a known metric and a target above 0; skipped"); continue
        cfg["titles"].append({"id": tid, "name": clean(raw.get("name") or tid, 32), "desc": clean(raw.get("description", ""), 120), "unlock": u})
    cfg["shop"] = parse_shop(data.get("shop"), warns)
    cfg["missions"] = parse_missions(data.get("missions"), warns)
    cfg["boot"] = parse_boot(data.get("boot"))
    cfg["retention"] = parse_retention(data.get("retention"), warns)
    ids = {"achievement": {a["id"] for a in cfg["achievements"]}, "bounty": {b["id"] for b in cfg["bounties"]},
           "quest": {q["id"] for q in cfg["quests"]}}
    for t in cfg["titles"]:
        u = t["unlock"]
        if u["type"] in ids and u["id"] not in ids[u["type"]]:
            warns.append(f"title '{t['id']}': refers to unknown {u['type']} '{u['id']}' (it can never unlock)")
    return cfg, warns

def game_level_curve(s) -> list:
    """Cumulative XP needed to reach each level (index 0 = level 1). Every level's cost is scaled by level_xp_multiplier."""
    xs, cum = [0], 0.0
    for n in range(1, int(s["level_cap"])):
        cum += max(1, round(s["level_base_xp"] * s["level_growth"] ** (n - 1) * s["level_xp_multiplier"]))
        xs.append(int(cum))
    return xs

def game_build_levels():
    GAME["level_xp"] = game_level_curve(GCFG["settings"])

def game_apply_config(cfg, warns, mtime):
    GCFG.clear()
    GCFG.update(cfg)
    GAME["mimap"] = {m["id"]: m for m in cfg["missions"]}
    GAME["warnings"], GAME["mtime"], GAME["cfg_error"] = warns, mtime, ""
    GAME["qmap"] = {q["id"]: q for q in cfg["quests"]}
    GAME["bmap"] = {b["id"]: b for b in cfg["bounties"]}
    GAME["amap"] = {a["id"]: a for a in cfg["achievements"]}
    GAME["tmap"] = {t["id"]: t for t in cfg["titles"]}
    GAME["smap"] = {i["id"]: i for i in cfg["shop"]}
    game_build_levels()

def game_load_config() -> str:
    """(Re)read the config file. Returns '' or a message. On a broken file the previous config stays."""
    path, mtime = GAME["cfg_path"], 0.0
    try:
        mtime = os.stat(path).st_mtime
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        if not GCFG:
            cfg, _ = parse_game_config({})
            game_apply_config(cfg, [f"'{path}' not found: using built-in XP/level rules with no quests, bounties, achievements or titles"], 0.0)
        return GAME["warnings"][0] if GAME["warnings"] else ""
    except (OSError, ValueError) as e:
        GAME["mtime"] = mtime or GAME["mtime"]
        GAME["cfg_error"] = f"game config not loaded ({e})"
        if not GCFG:
            cfg, _ = parse_game_config({})
            game_apply_config(cfg, [GAME["cfg_error"]], GAME["mtime"])
        return GAME["cfg_error"]
    cfg, warns = parse_game_config(data)
    game_apply_config(cfg, warns, mtime)
    return ""

# ---------------------------------------------------------------- profile state
def game_new_state() -> dict:
    return {"v": 1, "name": "Operator", "seed": os.urandom(4).hex(), "created": time.time(), "xp": 0, "title": "",
            "life": {}, "cats": [], "vendors": [], "max_in_range": 0, "longest_session": 0.0, "streak": 0,
            "best_streak": 0, "last_active": "", "ach": {}, "titles": {}, "bounties_done": {}, "bprog": {},
            "quests_done": {}, "day": {}, "log": [], "coins": {}, "missions": {},
            "shields": 0, "week": {}, "comeback_for": ""}

def game_load_state():
    path, base = GAME["profile_path"], game_new_state()
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            raise ValueError("not an object")
    except FileNotFoundError:
        data = {}
    except (OSError, ValueError) as e:
        try:
            os.replace(path, path + ".bak")
        except OSError:
            pass
        GAME["warnings"].append(f"profile '{path}' was unreadable ({e}); moved to .bak and started a new one")
        data = {}
    for k, default in base.items():
        v = data.get(k, default)
        base[k] = v if isinstance(v, type(default)) or (isinstance(default, float) and isinstance(v, int)) else default
    base["name"] = clean(base["name"], 24) or "Operator"
    base["xp"] = max(0, int(base["xp"]))
    base["shields"] = max(0, int(base["shields"]))
    STATE.clear()
    STATE.update(base)
    coin_state()                                   # fill in / repair the Intel Coins block
    GAME["vset"], GAME["cset"] = set(STATE["vendors"]), set(STATE["cats"])

def game_save(force=False):
    if not GAME["on"] or not (GAME["dirty"] or force):
        return
    try:
        tmp = GAME["profile_path"] + ".tmp"
        fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(STATE, f, indent=1)
        os.replace(tmp, GAME["profile_path"])
        GAME["dirty"], GAME["last_save"] = False, time.time()
    except OSError:
        pass

# ---------------------------------------------------------------- levels, day rollover, metrics
def game_level(xp=None) -> int:
    xp = STATE["xp"] if xp is None else xp
    return min(len(GAME["level_xp"]), bisect.bisect_right(GAME["level_xp"], xp))

def game_progress():
    """(level, xp into this level, xp needed for the next); need is 0 at the level cap."""
    lvl, xs = game_level(), GAME["level_xp"]
    if lvl >= len(xs):
        return lvl, 0, 0
    return lvl, STATE["xp"] - xs[lvl - 1], xs[lvl] - xs[lvl - 1]

def game_rank(level: int) -> str:
    name = ""
    for lv, nm in GCFG["ranks"]:
        if lv <= level:
            name = nm
    return name

def game_title_name() -> str:
    t = GAME["tmap"].get(STATE.get("title", ""))
    return t["name"] if t else ""

def game_day_key(now=None) -> str:
    t = datetime.datetime.fromtimestamp(now or time.time()) - datetime.timedelta(hours=GCFG["settings"]["day_rollover_hour"])
    return t.date().isoformat()

def game_pick_quests(key, level, prev, exclude=(), n=None):
    pool = [q for q in GCFG["quests"] if q["min_level"] <= level and q["id"] not in exclude]
    n = min(GCFG["settings"]["daily_quest_count"] if n is None else n, len(pool))
    fresh = [q for q in pool if q["id"] not in prev]
    if len(fresh) >= n:
        pool = fresh
    rng, chosen = random.Random(f"{key}|{STATE.get('seed', '')}"), []
    for _ in range(n):
        pick = rng.choices(pool, weights=[q["weight"] for q in pool])[0]
        chosen.append(pick["id"])
        pool.remove(pick)
    return chosen

def game_day() -> dict:
    key, d = game_day_key(), STATE["day"]
    if d.get("date") != key:
        prev = list(d.get("quests", []))
        STATE["day"] = d = {"date": key, "c": {}, "cats": [], "vendors": [], "max_in_range": 0, "xp_by": {},
                            "quests": [], "done": [], "active": False, "login": False, "bounties": {}}
        d["quests"] = game_pick_quests(key, game_level(), prev)
        GAME["dirty"] = True
    return d

def game_sync_quests():
    d = game_day()
    valid = [q for q in d["quests"] if q in GAME["qmap"]]
    want = GCFG["settings"]["daily_quest_count"]
    if len(valid) < want:
        valid += game_pick_quests(d["date"] + "+", game_level(), (), exclude=set(valid), n=want - len(valid))
    elif len(valid) > want:
        valid = valid[:want]
    if valid != d["quests"]:
        d["quests"] = valid
        GAME["dirty"] = True

def game_metric(name: str, scope: str = "life"):
    d = game_day()
    if name == "level":
        return game_level()
    if name == "total_xp":
        return STATE["xp"]
    if name == "streak_days":
        return STATE["streak"]
    if name == "achievements_unlocked":
        return len(STATE["ach"])
    if name == "longest_session_minutes":
        return STATE["longest_session"] if scope == "life" else d["c"].get("scan_minutes", 0)
    if name == "distinct_categories":
        return len(STATE["cats"] if scope == "life" else d["cats"])
    if name == "distinct_vendors":
        return len(STATE["vendors"] if scope == "life" else d["vendors"])
    if name == "max_in_range":
        return STATE["max_in_range"] if scope == "life" else d["max_in_range"]
    return (STATE["life"] if scope == "life" else d["c"]).get(name, 0)

def game_bump(name: str, n=1):
    if not GAME["on"]:
        return
    k = name.lower()
    STATE["life"][k] = STATE["life"].get(k, 0) + n
    d = game_day()
    d["c"][k] = d["c"].get(k, 0) + n
    GAME["dirty"] = True

def game_note(text: str, kind: str = "info", loud: bool = False):
    """Queue a message for the status line and keep it in the recent-activity log and session report."""
    ts = time.time()
    STATE["log"].append([ts, kind, text])
    del STATE["log"][:-40]
    GAME["session_log"].append((ts, kind, text))
    GAME["pending"].append((text, loud))
    log_event(text, "game")
    GAME["dirty"] = True

def game_grant(amount: int, why: str = ""):
    """Add XP (no caps). Announces level-ups and unlocks any level titles."""
    if not GAME["on"] or amount <= 0:
        return
    old = game_level()
    STATE["xp"] += int(amount)
    GAME["session_xp"] += int(amount)
    GAME["dirty"] = True
    new = game_level()
    if new > old:
        rank, prev_rank = game_rank(new), game_rank(old)
        extra = f" — new rank: {rank}" if rank and rank != prev_rank else ""
        cn = coins_for("level_up", new - old)
        game_note(f"⬆ LEVEL UP! You are now level {new}{extra}" + (f" (+{cn} {ci()})" if cn else ""), "level", False)
        game_fx("level", f"New rank: {rank}" if rank and rank != prev_rank else "", f"{STATE['xp']:,} total XP",
                f"+{cn} {ci()}" if cn else "", big2=str(new))

def game_xp(event: str, mult: int = 1) -> int:
    """XP for a gameplay event, using the config's value and its daily cap (if any)."""
    if not GAME["on"]:
        return 0
    amt = GCFG["xp_rules"].get(event, 0) * mult
    if amt <= 0:
        return 0
    surge = ret_cfg()["surge"]["multiplier"] if event != "daily_login" and surge_left() > 0 else 1.0
    if surge > 1.0:                                      # Daily Surge: your first minutes of the day pay extra
        amt = max(1, int(round(amt * surge)))
    cap = GCFG["xp_caps"].get(event)
    if cap is not None:
        d = game_day()
        used = d["xp_by"].get(event, 0)
        amt = min(amt, max(0, cap - used))
        if amt <= 0:
            capped = d.setdefault("capped", [])
            if event not in capped:                      # tell the player once per day instead of silently paying 0 XP
                capped.append(event)
                game_note(f"⛔ Daily XP cap reached for '{event}' ({cap} XP/day). It resets in {_until_reset()}. "
                          f"Raise or remove it under xp_caps in the game config.", "info", True)
            return 0
        d["xp_by"][event] = used + amt
    game_grant(amt, event)
    if surge > 1.0:
        dd = game_day()
        dd["surge_xp"] = dd.get("surge_xp", 0) + int(amt - amt / surge)
    return amt

# ---------------------------------------------------------------- event hooks (all no-ops when the game is off)
def game_session_start():
    if not GAME["on"]:
        return
    GAME["session_start_level"] = game_level()
    game_bump("sessions")
    d = game_day()
    if not d["login"]:
        d["login"] = True
        got = game_xp("daily_login")
        cn = coins_for("daily_login")
        if got:
            game_note(f"☀ Daily check-in: +{got} XP" + (f", +{cn} {ci()}" if cn else "") + ". Press p for today's quests.", "info")
    game_session_hooks(d)

def game_on_new_device(dev):
    if not GAME["on"]:
        return
    key = dev.ghost_id or dev.mac
    if key in GAME["credited"]:
        return
    GAME["credited"].add(key)
    i, d = dev.ident, game_day()
    game_bump("devices_seen")
    game_xp("new_device")
    per = int(GCFG["settings"]["devices_per_coin"])
    if per > 0 and int(STATE["life"].get("devices_seen", 0)) % per == 0:
        coins_for("device_batch")
    cat = i.category
    game_bump(f"category:{cat}")
    if cat not in GAME["cset"]:
        GAME["cset"].add(cat)
        STATE["cats"].append(cat)
        got_xp = game_xp("new_category")
        cn = coins_for("new_category")
        if got_xp:
            game_note(f"{CATEGORY_ICONS.get(cat, '🔹')} First {cat.replace('_', ' ')} device discovered" + (f" (+{cn} {ci()})" if cn else ""), "info")
    if cat not in d["cats"]:
        d["cats"].append(cat)
    v = norm(clean(i.vendor, 40)) if i.vendor else ""
    if v:
        game_bump(f"vendor:{v}")
        if v not in GAME["vset"] and len(STATE["vendors"]) < 3000:
            GAME["vset"].add(v)
            STATE["vendors"].append(v)
            game_xp("new_vendor")
        if v not in d["vendors"]:
            d["vendors"].append(v)
    if i.tier:
        game_bump(f"tier:{i.tier}")
    game_bump(f"addr:{i.addr_type}")

def game_on_flag(dev):
    if not GAME["on"]:
        return
    key = ("flag", dev.ghost_id or dev.mac)
    if key in GAME["credited"]:
        return
    GAME["credited"].add(key)
    if dev.ident.tier == "alert":
        game_bump("alerts_found")
        game_xp("alert_device")
        coins_for("alert_device")
    elif dev.ident.tier == "possible":
        game_bump("possibles_found")
        game_xp("possible_device")
        coins_for("possible_device")

def game_on_follower(t):
    if not GAME["on"]:
        return
    game_bump("followers_flagged")
    game_xp("follower_alert")
    coins_for("follower_alert")

def game_on_hunt(done: bool):
    if not GAME["on"]:
        return
    game_bump("hunts_completed" if done else "hunts_started")
    if done:
        game_xp("hunt_completed")
        coins_for("hunt_completed")

def game_on_rotation():
    if GAME["on"]:
        game_bump("rotations_linked")
        game_xp("rotation_linked")

# ---------------------------------------------------------------- bounties, quests, achievements, titles
def bounty_matches(rule: dict, dev) -> bool:
    i = dev.ident
    if "category" in rule and i.category.lower() not in rule["category"]:
        return False
    if "tier" in rule and (i.tier or "none").lower() not in rule["tier"]:
        return False
    if "addr_type" in rule and i.addr_type.lower() not in rule["addr_type"]:
        return False
    if "vendor" in rule and not (i.vendor and rule["vendor"].search(i.vendor)):
        return False
    if "name" in rule and not (dev.name and rule["name"].search(dev.name)):
        return False
    if "label" in rule and not (i.label and rule["label"].search(i.label)):
        return False
    if "uuid" in rule and not (rule["uuid"] & dev.uuids):
        return False
    if "mfg" in rule and not (rule["mfg"] & dev.mfg_ids):
        return False
    if "min_rssi" in rule and dev.ema < rule["min_rssi"]:
        return False
    if "followed" in rule:
        tail = TAILS.get(dev.mac)
        if bool(tail and FOLLOW_RANK[tail.tier] >= 2) != rule["followed"]:
            return False
    return True

def bounty_state(b):
    """(done, found_so_far) for the current period (forever for 'once', today for 'daily')."""
    if b["repeat"] == "once":
        return b["id"] in STATE["bounties_done"], len(STATE["bprog"].get(b["id"], []))
    e = game_day()["bounties"].get(b["id"], {})
    return bool(e.get("done")), len(e.get("keys", []))

def game_eval_bounties(now):
    open_b = [b for b in GCFG["bounties"] if not bounty_state(b)[0]]
    if not open_b:
        return
    day, closed = game_day(), set()
    for dev in DEVICES.values():
        if not dev.counted or now - dev.last > 5.0:
            continue
        key = dev.ghost_id or dev.mac
        for b in open_b:
            if b["id"] in closed:
                continue
            if b["repeat"] == "once":
                keys = STATE["bprog"].setdefault(b["id"], [])
            else:
                keys = day["bounties"].setdefault(b["id"], {"keys": [], "done": False})["keys"]
            if key in keys or not bounty_matches(b["match"], dev):
                continue
            keys.append(key)
            GAME["dirty"] = True
            if len(keys) >= b["count"]:
                closed.add(b["id"])
                game_claim_bounty(b)

def game_claim_bounty(b):
    STATE["bounties_done"][b["id"]] = time.time()          # last claim (titles check this)
    if b["repeat"] == "daily":
        game_day()["bounties"][b["id"]]["done"] = True
    game_bump("bounties_claimed")
    game_grant(b["xp"], f"bounty {b['id']}")
    cn = coins_grant(bounty_coins(b), f"bounty {b['id']}")
    game_note(f"💰 BOUNTY CLAIMED: {b['name']} (+{b['xp']} XP" + (f", +{cn} {ci()}" if cn else "") + ")", "bounty", False)
    game_fx("bounty", b["name"], BOUNTY_DIFF[b["difficulty"]][0].title() + " bounty" + (" · " + b["desc"] if b["desc"] else ""), reward_text(b["xp"], cn))

def quest_progress(q):
    return min(float(q["target"]), float(game_metric(q["metric"], "day")))

def game_eval_quests():
    d = game_day()
    for qid in list(d["quests"]):
        q = GAME["qmap"].get(qid)
        if q is None or qid in d["done"]:
            continue
        if game_metric(q["metric"], "day") >= q["target"]:
            d["done"].append(qid)
            STATE["quests_done"][qid] = STATE["quests_done"].get(qid, 0) + 1
            game_bump("quests_completed")
            game_grant(q["xp"], f"quest {qid}")
            cn = coins_grant(quest_coins(q), f"quest {qid}")
            game_note(f"✅ QUEST COMPLETE: {q['name']} (+{q['xp']} XP" + (f", +{cn} {ci()}" if cn else "") + ")", "quest", False)
            game_fx("quest", q["name"], q["desc"], reward_text(q["xp"], cn))
            left = sum(1 for x in d["quests"] if x not in d["done"] and x in GAME["qmap"])
            if left == 0:
                bonus = coins_for("all_quests_done")
                game_note("🌟 All daily quests complete! Come back tomorrow for new ones." + (f" Bonus +{bonus} {ci()}" if bonus else ""), "quest")

def game_eval_achievements():
    for a in GCFG["achievements"]:
        if a["id"] in STATE["ach"]:
            continue
        if game_metric(a["metric"], "life") >= a["target"]:
            STATE["ach"][a["id"]] = time.time()
            game_grant(a["xp"], f"achievement {a['id']}")
            cn = coins_grant(achievement_coins(a), f"achievement {a['id']}")
            game_note(f"{a['icon']} ACHIEVEMENT: {a['name']} (+{a['xp']} XP" + (f", +{cn} {ci()}" if cn else "") + ")", "achievement", False)
            game_fx("achievement", f"{a['icon']} {a['name']}", a["desc"], reward_text(a["xp"], cn))

def title_unlocked_now(t) -> bool:
    u = t["unlock"]
    typ = u["type"]
    if typ == "always":
        return True
    if typ == "level":
        return game_level() >= u["value"]
    if typ == "achievement":
        return u["id"] in STATE["ach"]
    if typ == "bounty":
        return u["id"] in STATE["bounties_done"]
    if typ == "quest":
        return STATE["quests_done"].get(u["id"], 0) > 0
    if typ == "metric":
        return game_metric(u["metric"], "life") >= u["target"]
    return False

def game_eval_titles():
    for t in GCFG["titles"]:
        if t["id"] in STATE["titles"] or not title_unlocked_now(t):
            continue
        STATE["titles"][t["id"]] = time.time()
        if not STATE["title"]:
            STATE["title"] = t["id"]
        if t["unlock"]["type"] != "always" or STATE["life"].get("sessions", 0) > 1:
            game_note(f"🏷 TITLE UNLOCKED: {t['name']} (press t to equip)", "title", False)
            game_fx("title", t["name"], t["desc"] or _req_text(t), "Press t to equip")
        GAME["dirty"] = True

def game_activate_day(d):
    d["active"] = True
    today = datetime.date.fromisoformat(d["date"])
    last = STATE.get("last_active")
    prev_streak = STATE["streak"]
    s, R = GCFG["settings"], ret_cfg()
    saved = 0
    if last:
        gap = (today - datetime.date.fromisoformat(last)).days
        if gap == 1:
            STATE["streak"] += 1
        elif gap > 1:
            missed = gap - 1
            if prev_streak > 0 and STATE["shields"] >= missed:     # Streak Shields cover the missed days
                STATE["shields"] -= missed
                saved = missed
                STATE["streak"] += 1
                game_bump("shields_used", missed)
            else:
                STATE["streak"] = 1
    else:
        STATE["streak"] = 1
    new_day = last != d["date"]
    STATE["last_active"] = d["date"]
    STATE["best_streak"] = max(STATE["best_streak"], STATE["streak"])
    if new_day:
        game_bump("active_days")
    if saved:
        game_note(f"🛡 STREAK SHIELD USED: it covered {saved} missed day(s) and your {STATE['streak']}-day streak lives. "
                  f"{STATE['shields']} shield(s) left.", "streak", True)
    ms = streak_milestone_xp(STATE["streak"]) if STATE["streak"] != prev_streak else 0
    lad = R["streak_ladder"]
    lc = coins_grant(lad[(STATE["streak"] - 1) % len(lad)], f"streak day {STATE['streak']}") if (lad and new_day and not ms) else 0
    if STATE["streak"] > 1 and s["streak_bonus_xp"]:
        bonus = s["streak_bonus_xp"] * min(STATE["streak"], s["streak_bonus_cap"])
        game_grant(bonus, "streak")
        game_note(f"🔥 {STATE['streak']}-day streak! +{bonus} XP" + (f", +{lc} {ci()}" if lc else ""), "info", True)
    elif lc:
        game_note(f"🔥 Day {STATE['streak']} counted: +{lc} {ci()}", "info", True)
    if ms:
        game_grant(ms, f"streak milestone {STATE['streak']}")
        cn = coins_grant(max(1, round(ms / s["streak_xp_per_coin"])), f"streak {STATE['streak']}")
        game_note(f"🏆 {STATE['streak']}-DAY STREAK MILESTONE! +{ms} XP" + (f", +{cn} {ci()}" if cn else ""), "streak", False)
        game_fx("streak", f"🔥 {STATE['streak']}-DAY STREAK", "Scanning every day pays off", reward_text(ms, cn), big2=str(STATE["streak"]))
    fe = R["shield"]["free_every"]
    if fe and STATE["streak"] != prev_streak and STATE["streak"] % fe == 0 and shield_add(1):
        game_note(f"🛡 Free Streak Shield for a {STATE['streak']}-day streak ({STATE['shields']}/{shield_max()} held)", "streak", True)
    GAME["dirty"] = True

# ---------------------------------------------------------------- daily hooks: surge, shields, caches, weekly ops, welcome back
def ret_cfg() -> dict:
    return GCFG.get("retention") or RETENTION_DEFAULT

def shield_max() -> int:
    return int(ret_cfg()["shield"]["max"])

def shield_add(n: int = 1) -> int:
    """Give Streak Shields up to the carry limit. Returns how many were actually added."""
    got = max(0, min(int(n), shield_max() - STATE["shields"]))
    if got:
        STATE["shields"] += got
        GAME["dirty"] = True
    return got

def surge_left() -> float:
    """Seconds of today's Daily Surge still unused. The clock only runs while you scan. 0 once it's over or switched off."""
    if not GAME["on"]:
        return 0.0
    sg = ret_cfg()["surge"]
    if not sg["enabled"] or sg["multiplier"] <= 1.0:
        return 0.0
    return max(0.0, sg["minutes"] * 60.0 - game_day()["c"].get("scan_minutes", 0) * 60.0)

def _clock(sec: float) -> str:
    return f"{int(sec // 60)}:{int(sec % 60):02d}"

def cache_roll(t: dict):
    xp, coins = random.randint(*t["xp"]), random.randint(*t["coins"])
    jackpot = t["jackpot_chance"] > 0 and random.random() < t["jackpot_chance"]
    if jackpot:
        xp, coins = int(xp * t["jackpot_mult"]), int(coins * t["jackpot_mult"])
    return xp, coins, (t["shield_chance"] > 0 and random.random() < t["shield_chance"]), jackpot

def cache_open(t: dict, why: str):
    """Open a Daily Cache / Weekly Chest: a random reward of XP and coins, sometimes a Streak Shield, rarely a jackpot."""
    xp, coins, shield, jackpot = cache_roll(t)
    game_grant(xp, f"cache {t.get('id', 'weekly')}")
    cn = coins_grant(coins, t["name"])
    sh = shield_add(1) if shield else 0
    if shield and not sh:                                  # already carrying the max: pay coins instead
        cn += coins_grant(5, "shield overflow")
    game_bump("caches_opened")
    bits = [f"+{xp} XP"] + ([f"+{cn} {ci()}"] if cn else []) + (["+1 🛡 shield"] if sh else [])
    game_note(f"📦 {t['name'].upper()} OPENED" + (" · JACKPOT!" if jackpot else "") + ": " + ", ".join(bits), "cache", False)
    game_fx("cache", t["name"], ("JACKPOT! " if jackpot else "") + why, " · ".join(bits))

def game_check_caches():
    """Open every Daily Cache whose quest count has been reached (once per day each)."""
    if not GAME["on"]:
        return
    d = game_day()
    valid = [q for q in d["quests"] if q in GAME["qmap"]]
    if not valid:
        return
    done = sum(1 for q in valid if q in d["done"])
    opened = d.setdefault("caches", [])
    for t in ret_cfg()["caches"]:
        if t["id"] in opened:
            continue
        need = len(valid) if t["quests"] == "all" else min(t["quests"], len(valid))
        if done >= need:
            opened.append(t["id"])
            GAME["dirty"] = True
            cache_open(t, f"{need} daily quest(s) done")

def game_week_key(now=None) -> str:
    y, w, _ = datetime.date.fromisoformat(game_day_key(now)).isocalendar()
    return f"{y}-W{w:02d}"

def week_left_text() -> str:
    """Time until the weekly reset (Monday at the day-rollover hour)."""
    h = GCFG["settings"]["day_rollover_hour"]
    now = datetime.datetime.now()
    adj = now - datetime.timedelta(hours=h)
    nxt = datetime.datetime.combine(adj.date() + datetime.timedelta(days=7 - adj.weekday()), datetime.time()) + datetime.timedelta(hours=h)
    d, rem = divmod(max(0, int((nxt - now).total_seconds())), 86400)
    return f"{d}d {rem // 3600}h" if d else f"{rem // 3600}h {rem % 3600 // 60}m"

def weekly_pick(key: str, level: int, prev, exclude=(), n=None) -> list:
    R = ret_cfg()
    want = R["weekly_count"] if n is None else n
    pool = [g for g in R["weekly"] if g["min_level"] <= level and g["id"] not in exclude]
    chosen = [g["id"] for g in pool if g["always"]][:want]
    rest = [g for g in pool if not g["always"]]
    need = max(0, min(want - len(chosen), len(rest)))
    fresh = [g for g in rest if g["id"] not in prev]
    if len(fresh) >= need:
        rest = fresh
    rng = random.Random(f"week|{key}|{STATE.get('seed', '')}")
    for _ in range(need):
        pick = rng.choice(rest)
        chosen.append(pick["id"])
        rest.remove(pick)
    return chosen

def game_week() -> dict:
    """This week's ops. Rolls over every Monday and keeps itself in step with config edits."""
    R, key, w = ret_cfg(), game_week_key(), STATE.get("week")
    if not isinstance(w, dict) or w.get("key") != key:
        prev = list(w.get("goals", [])) if isinstance(w, dict) else []
        w = STATE["week"] = {"key": key, "goals": [], "base": {}, "done": [], "chest": False}
        w["goals"] = weekly_pick(key, game_level(), prev)
        GAME["dirty"] = True
    wmap = {g["id"]: g for g in R["weekly"]}
    valid = [g for g in w["goals"] if g in wmap]
    if len(valid) < R["weekly_count"]:
        valid += weekly_pick(key + "+", game_level(), (), exclude=set(valid), n=R["weekly_count"] - len(valid))
    elif len(valid) > R["weekly_count"]:
        valid = valid[:R["weekly_count"]]
    if valid != w["goals"]:
        w["goals"] = valid
        GAME["dirty"] = True
    base = w.setdefault("base", {})
    for gid in w["goals"]:
        m = wmap[gid]["metric"]
        if m not in base:                                  # progress counts from when the week (or the goal) began
            base[m] = game_metric(m, "life")
            GAME["dirty"] = True
    return w

def weekly_progress(g: dict, w: dict) -> float:
    return max(0.0, min(float(g["target"]), float(game_metric(g["metric"], "life")) - float(w["base"].get(g["metric"], 0))))

def weekly_coins(g: dict) -> int:
    return g["coins"] if g.get("coins") is not None else (max(1, round(g["xp"] / 10)) if g["xp"] > 0 else 0)

def game_eval_weekly():
    if not GAME["on"]:
        return
    R = ret_cfg()
    w = game_week()
    wmap = {g["id"]: g for g in R["weekly"]}
    for gid in w["goals"]:
        g = wmap.get(gid)
        if g is None or gid in w["done"]:
            continue
        if weekly_progress(g, w) >= g["target"]:
            w["done"].append(gid)
            game_bump("weekly_goals_done")
            game_grant(g["xp"], f"weekly {gid}")
            cn = coins_grant(weekly_coins(g), f"weekly {gid}")
            game_note(f"🗓 WEEKLY OP COMPLETE: {g['name']} (+{g['xp']} XP" + (f", +{cn} {ci()}" if cn else "") + ")", "quest", False)
            game_fx("quest", g["name"], "Weekly op" + (" · " + g["desc"] if g["desc"] else ""), reward_text(g["xp"], cn))
    chest = R["weekly_chest"]
    if w["goals"] and not w["chest"] and chest.get("enabled", True) and all(x in w["done"] for x in w["goals"] if x in wmap):
        w["chest"] = True
        cache_open(chest, "every weekly op done")

def game_eval_surge_end():
    """Once per day, say how much the Daily Surge added when it runs out."""
    d = game_day()
    sg = ret_cfg()["surge"]
    if d.get("surge_end") or not sg["enabled"] or sg["multiplier"] <= 1.0 or d["c"].get("scan_minutes", 0) <= 0 or surge_left() > 0:
        return
    d["surge_end"] = True
    GAME["dirty"] = True
    if d.get("surge_xp", 0) > 0:
        game_note(f"⚡ Daily Surge over: it added +{d['surge_xp']} XP today. It's back tomorrow.", "info", False)

def game_session_hooks(d):
    """Launch-time hooks: Welcome Back bonus, plus one line about today's Surge, shields and the week."""
    if not GAME["on"]:
        return
    R = ret_cfg()
    cb, last = R["comeback"], STATE.get("last_active")
    if last and cb["min_days_away"] > 0 and STATE.get("comeback_for") != last:
        try:
            gap = (datetime.date.fromisoformat(d["date"]) - datetime.date.fromisoformat(last)).days
        except ValueError:
            gap = 0
        if gap >= cb["min_days_away"]:
            STATE["comeback_for"] = last
            game_grant(cb["xp"], "welcome back")
            cn = coins_grant(cb["coins"], "welcome back")
            game_note(f"👋 Welcome back, operator! {gap} days away: +{cb['xp']} XP" + (f", +{cn} {ci()}" if cn else ""), "streak", True)
    bits = []
    sl = surge_left()
    if sl > 0:
        bits.append(f"⚡ Surge x{R['surge']['multiplier']:g} discovery XP for {sl / 60:.0f} more min of scanning")
    w = game_week()
    wmap = {g["id"]: g for g in R["weekly"]}
    goals = [g for g in w["goals"] if g in wmap]
    if goals:
        bits.append(f"🗓 Weekly ops {sum(1 for g in goals if g in w['done'])}/{len(goals)} ({week_left_text()} left)")
    if STATE["shields"]:
        bits.append(f"🛡 {STATE['shields']} shield(s)")
    if bits:
        game_note(" · ".join(bits), "info")

def cache_status_text() -> Text:
    """One or two lines for the quests page: Daily Surge and the Daily Caches."""
    R, d = ret_cfg(), game_day()
    valid = [q for q in d["quests"] if q in GAME["qmap"]]
    done = sum(1 for q in valid if q in d["done"])
    t = Text()
    sl = surge_left()
    if R["surge"]["enabled"] and R["surge"]["multiplier"] > 1.0:
        if sl > 0:
            t.append(f"⚡ Daily Surge x{R['surge']['multiplier']:g} discovery XP: {_clock(sl)} of scanning left\n", style="bold bright_cyan")
        else:
            t.append("⚡ Daily Surge used up for today (back after the daily reset)\n", style="dim")
    if R["caches"] and valid:
        t.append("📦 Daily caches: ", style="bold")
        for i, c in enumerate(R["caches"]):
            need = len(valid) if c["quests"] == "all" else min(c["quests"], len(valid))
            opened = c["id"] in d.get("caches", [])
            if i:
                t.append("  ·  ", style="dim")
            t.append(f"{c['name']} {min(done, need)}/{need}" + (" ✓" if opened else ""), style="green" if opened else "dim")
    return t

def _profile_page_weekly(size) -> Group:
    R, w = ret_cfg(), game_week()
    wmap = {g["id"]: g for g in R["weekly"]}
    t = Table(box=ROUNDED, expand=True)
    t.add_column("", width=2, no_wrap=True)
    t.add_column("Weekly op", ratio=3, overflow="fold")
    t.add_column("Progress", width=30, no_wrap=True)
    t.add_column("Reward", width=12, justify="right", no_wrap=True)
    goals = [wmap[g] for g in w["goals"] if g in wmap]
    for g in goals:
        done = g["id"] in w["done"]
        prog = weekly_progress(g, w)
        cell = Text(g["name"], style="green" if done else "bold")
        if g["desc"]:
            cell.append("\n" + g["desc"], style="dim")
        bar = Text()
        bar.append_text(mini_bar(prog / g["target"], 14, "green" if done else "cyan"))
        bar.append(f" {_fmt_num(prog)}/{_fmt_num(g['target'])}", style="dim")
        t.add_row(Text("✓" if done else "○", style="green" if done else "dim"), cell, bar,
                  Text(f"+{g['xp']} XP\n+{weekly_coins(g)} {ci()}", style="yellow"))
    if not goals:
        t.add_row("", Text("No weekly ops configured (see the retention block in the game config).", style="dim"), "", "")
    chest = R["weekly_chest"]
    foot = Text(f"Resets in {week_left_text()} · {sum(1 for g in goals if g['id'] in w['done'])}/{len(goals)} done", style="dim")
    if chest.get("enabled", True) and goals:
        foot.append(f" · 🎁 {chest['name']} " + ("opened ✓" if w.get("chest") else "opens when every op is done"), style="green" if w.get("chest") else "bold yellow")
    lad = R["streak_ladder"]
    ladder = Text()
    if lad:
        st_state, st_n = streak_status()
        cur = (STATE["streak"] - 1) % len(lad) if st_state == "active" else STATE["streak"] % len(lad)
        ladder.append("Streak ladder (coins per streak day): ", style="bold")
        for i, v in enumerate(lad[:14]):
            ladder.append(f"{i + 1}:{v} ", style="bold bright_yellow" if i == cur else "dim")
        if len(lad) > 14:
            ladder.append("…", style="dim")
        ladder.append(" (repeats)", style="dim")
    fe = R["shield"]["free_every"]
    shields = Text(f"🛡 Streak Shields {STATE['shields']}/{shield_max()}: each covers one missed day automatically. "
                   + (f"Earn one every {fe} streak days, " if fe else "") + "from caches, or buy them in the Coin Exchange (e).", style="cyan")
    return Group(t, foot, Text(""), ladder, shields)

def game_flush():
    p = GAME["pending"]
    if not p:
        return
    GAME["pending"] = []
    texts = [t for t, _ in p]
    msg = " · ".join(texts[:3]) + (f"  (+{len(texts) - 3} more, press p)" if len(texts) > 3 else "")
    STATUS.set(msg)
    if any(loud for _, loud in p):
        play_notification_sound()

def game_tick(now: float, dt: float):
    """Called every UI tick (~4x/s): cheap counters every tick, full evaluation about once a second."""
    if not GAME["on"]:
        return
    if now - GAME["last_check"] >= 5.0:
        GAME["last_check"] = now
        try:
            m = os.stat(GAME["cfg_path"]).st_mtime
        except OSError:
            m = 0.0
        if m and m != GAME["mtime"]:
            err = game_load_config()
            game_sync_quests()
            STATUS.set(err or f"Game config reloaded: {len(GCFG['quests'])} quests, {len(GCFG['bounties'])} bounties, "
                              f"{len(GCFG['achievements'])} achievements, {len(GCFG['titles'])} titles"
                              + (f" ({len(GAME['warnings'])} warnings, see --check-game)" if GAME["warnings"] else ""))
    if dt > 0:
        game_bump("scan_minutes", dt / 60.0)
        GAME["scan_acc"] += dt
        GAME["session_scan_s"] += dt
        while GAME["scan_acc"] >= 60.0:
            GAME["scan_acc"] -= 60.0
            game_xp("scan_minute")
            GAME["scan_min_n"] += 1
            dd = game_day()
            dd["scan_mins"] = dd.get("scan_mins", 0) + 1       # per day (not per session), so short sessions add up
            if dd["scan_mins"] % 60 == 0:
                coins_for("scan_hour")
        STATE["longest_session"] = max(STATE["longest_session"], GAME["session_scan_s"] / 60.0)
    pk = STATS["packets"] - GAME["last_packets"]
    if pk > 0:
        GAME["last_packets"] = STATS["packets"]
        game_bump("packets", pk)
    if now - GAME["last_eval"] >= 1.0:
        GAME["last_eval"] = now
        d = game_day()
        n = sum(1 for x in DEVICES.values() if x.counted and now - x.last <= CFG["stale"])
        if n > d["max_in_range"]:
            d["max_in_range"] = n
        if n > STATE["max_in_range"]:
            STATE["max_in_range"] = n
            GAME["dirty"] = True
        if not d["active"] and d["c"].get("scan_minutes", 0) >= GCFG["settings"]["streak_min_scan_minutes"]:
            game_activate_day(d)
        game_eval_bounties(now)
        game_eval_quests()
        game_check_caches()
        game_eval_weekly()
        game_eval_surge_end()
        game_eval_achievements()
        game_eval_titles()
    game_flush()
    if GAME["dirty"] and now - GAME["last_save"] >= 20.0:
        game_save()

# ---------------------------------------------------------------- init / CLI helpers
def game_init(cfg_path, profile_path, player=None) -> list:
    """Load config + profile and switch the game on. Returns startup warnings."""
    GAME["cfg_path"], GAME["profile_path"] = cfg_path, profile_path
    game_load_config()
    game_load_state()
    if player:
        STATE["name"] = clean(player, 24) or STATE["name"]
    GAME["on"] = True
    GAME["last_packets"] = 0
    game_sync_quests()
    game_eval_titles()
    GAME["pending"].clear()
    GAME["session_log"].clear()
    GAME["dirty"] = True
    game_save(force=True)
    return GAME["warnings"] + ([GAME["cfg_error"]] if GAME["cfg_error"] else [])

def check_game_config(path) -> int:
    """--check-game: validate the config, print a summary and the metric reference."""
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"[!] {path} not found.")
        return 1
    except ValueError as e:
        print(f"[!] {path} is not valid JSON: {e}")
        return 1
    cfg, warns = parse_game_config(data)
    s = cfg["settings"]
    print(f"[+] {path}: {len(cfg['quests'])} quests, {len(cfg['bounties'])} bounties, "
          f"{len(cfg['achievements'])} achievements, {len(cfg['titles'])} titles, {len(cfg['ranks'])} ranks")
    xs = game_level_curve(s)
    marks = [lv for lv in (5, 10, 25, 50, int(s["level_cap"])) if lv <= len(xs)]
    print("[+] Total XP needed: " + ", ".join(f"Lv{lv}={xs[lv - 1]:,}" for lv in marks))
    print(f"[+] Daily quests per day: {s['daily_quest_count']} (from a pool of {len(cfg['quests'])})")
    print(f"[+] Intel Coins ({s['coin_icon']}): {len(cfg['shop'])} shop items, prices {min((i['price'] for i in cfg['shop']), default=0):,} to "
          f"{max((i['price'] for i in cfg['shop']), default=0):,}; "
          f"quests pay about XP/{s['quest_xp_per_coin']:g}, achievements XP/{s['achievement_xp_per_coin']:g}, bounties {'/'.join(str(cfg['coin_rules'].get('bounty_' + d, 0)) for d in BOUNTY_DIFF)}")
    print(f"[+] Missions: {len(cfg['missions'])} (" + ", ".join(f"{m['name']} {fmt_dur(m['time'], True)}" for m in cfg["missions"][:6]) + ("..." if len(cfg["missions"]) > 6 else "") + ")")
    bt = cfg["boot"]
    print(f"[+] Boot sequence: {'on' if bt['enabled'] else 'off'}, speed x{bt['speed']:g}, banner {bt['banner']!r}, intro sound {'on' if bt['play_intro'] else 'off'}, {len(bt['lines'])} extra line(s)")
    rt = cfg["retention"]
    print(f"[+] Daily hooks: surge {'x%g for %g min' % (rt['surge']['multiplier'], rt['surge']['minutes']) if rt['surge']['enabled'] else 'off'}, "
          f"{len(rt['caches'])} daily cache(s), streak ladder {rt['streak_ladder']}, shields up to {rt['shield']['max']} "
          f"(free every {rt['shield']['free_every']} days), welcome back after {rt['comeback']['min_days_away']} days, "
          f"{rt['weekly_count']} of {len(rt['weekly'])} weekly ops per week")
    for w in warns:
        print(f"[!] {w}")
    if not warns:
        print("[+] No problems found.")
    print("\nMetrics you can use in quests, achievements and title unlocks:")
    for k, v in GAME_METRICS.items():
        print(f"  {k:<24} {v}")
    for k, v in GAME_METRIC_PREFIXES.items():
        print(f"  {k + '<name>':<24} {v}")
    print("\nXP events you can set in xp_rules / xp_caps: " + ", ".join(GAME_XP_EVENTS))
    print("Coin events you can set in coin_rules / coin_caps: " + ", ".join(GAME_COIN_EVENTS))
    print("Shop: each entry in \"shop\" with a known id edits that item (name, description, price, min_level, hidden, enabled:false, spec); a new id adds a "
          "'theme' (spec.mode mono/duo/cycle + #rrggbb colors) or a 'glitch' (spec.kinds from " + ", ".join(GLITCH_KINDS) + ", spec.level 1-3).")
    print("Shop items: " + ", ".join(f"{i['id']} ({i['price']})" for i in cfg["shop"]))
    print("Bounty match keys: category, tier, addr_type, vendor, name, label, uuid, mfg, min_rssi, followed")
    print("Mission objectives: {distinct: " + "/".join(MISSION_DISTINCT) + ", target}, {match: <bounty match keys>, [distinct], target}, or {metric: <counter>, target}")
    print("Mission counters: " + ", ".join(MISSION_COUNTER_METRICS) + ", " + ", ".join(p + "<x>" for p in MISSION_COUNTER_PREFIXES))
    print("Mission fields: id, name, description, time (seconds) or minutes, difficulty, xp, coins, min_level, repeat (" + "/".join(MISSION_REPEAT) + "), scope (" + "/".join(MISSION_SCOPES) + "), objectives (1-4)")
    return 0

# ---------------------------------------------------------------- profile view (overlay)
# ---------------------------------------------------------------- streak milestones
# Bonus XP when a daily streak reaches these days. Specials below win; otherwise every 7th day pays 150 x weeks (max 1500).
STREAK_SPECIAL = {3: 50, 30: 750, 60: 1500, 90: 2500, 100: 3000, 180: 5000, 365: 10000}

def streak_milestone_xp(n: int) -> int:
    """Bonus XP for reaching a streak of n days (0 = not a milestone)."""
    if n in STREAK_SPECIAL:
        return STREAK_SPECIAL[n]
    if n >= 7 and n % 7 == 0:
        return min(150 * (n // 7), 1500)
    return 0

def next_streak_milestone(n: int):
    """(day, xp) of the next milestone after a streak of n days."""
    m = n + 1
    while streak_milestone_xp(m) == 0:
        m += 1
    return m, streak_milestone_xp(m)

def streak_status():
    """(state, days) for today: 'active' (streak counted today), 'risk' (yesterday counted, today not yet) or 'none'."""
    d = game_day()
    if d["active"]:
        return "active", STATE["streak"]
    last = STATE.get("last_active")
    if last:
        try:
            gap = (datetime.date.fromisoformat(d["date"]) - datetime.date.fromisoformat(last)).days
        except ValueError:
            gap = 99
        if gap == 1:
            return "risk", STATE["streak"]
        if gap <= 0:
            return "active", STATE["streak"]
        if STATE["streak"] > 0 and STATE["shields"] >= gap - 1:
            return "shield", STATE["streak"]
    return "none", 0

def game_strip_text(now: float):
    """HUD 'almost there' strip: closest quests/bounties to finishing, plus the daily streak. None when the game is off."""
    if not GAME["on"]:
        return None
    d = game_day()
    cands = []
    for qid in d["quests"]:
        q = GAME["qmap"].get(qid)
        if q is not None and qid not in d["done"]:
            cands.append((quest_progress(q) / q["target"], "🗒", q["name"], quest_progress(q), q["target"]))
    for b in GCFG["bounties"]:
        done, found = bounty_state(b)
        if not done and found > 0:
            cands.append((found / b["count"], "💰", b["name"], found, b["count"]))
    cands.sort(key=lambda c: -c[0])
    shown = [c for c in cands if c[0] > 0][:2] or cands[:1]
    t = Text(no_wrap=True, overflow="ellipsis")
    t.append("🎯 Almost there: ", style="bold bright_yellow")
    if shown:
        for i, (frac, icon, name, cur, tgt) in enumerate(shown):
            if i:
                t.append("  ·  ", style="dim")
            t.append(f"{icon} {clean(name, 24)} ", style="bright_white")
            t.append_text(mini_bar(frac, 6, "green" if frac >= 0.75 else "cyan"))
            t.append(f" {_fmt_num(cur)}/{_fmt_num(tgt)}", style="green" if frac >= 0.75 else "dim")
    else:
        t.append("🌟 all of today's quests are done", style="green")
    t.append("  │  ", style="dim")
    state, n = streak_status()
    need = GCFG["settings"]["streak_min_scan_minutes"]
    left = max(0.0, need - d["c"].get("scan_minutes", 0))
    if state == "active":
        m, xp = next_streak_milestone(n)
        t.append(f"🔥 Day {n}", style="bold dark_orange")
        t.append(f" → Day {m}: +{xp} XP in {m - n}d", style="dim")
        if STATE["shields"]:
            t.append(f"  🛡{STATE['shields']}", style="cyan")
    elif state == "risk":
        t.append(f"🔥 {n}-day streak at risk", style="bold red")
        t.append(f": scan {left:.0f} more min to keep it" if left >= 0.5 else ": keep scanning", style="dim")
    elif state == "shield":
        t.append(f"🔥 {n}-day streak held by 🛡", style="bold cyan")
        t.append(f": scan {left:.0f} more min to spend a shield and keep it" if left >= 0.5 else ": keep scanning", style="dim")
    else:
        t.append("🔥 No streak yet", style="dim")
        t.append(f": scan {need:g} min today to start one", style="dim")
    return t

def game_hud_text():
    if not GAME["on"]:
        return None
    now = time.time()
    animated = CFG["fx"] and XPANIM["disp"] is not None
    lvl, into, need = game_progress_at(XPANIM["disp"]) if animated else game_progress()
    t = Text(no_wrap=True, overflow="ellipsis")
    t.append(f"🏅 Lv {lvl} ", style="bold yellow")
    t.append_text(xp_bar(into / need if need else 1.0, 10, now))
    t.append(f" {int(round(into))}/{need} XP" if need else " MAX", style="yellow")
    if animated and XPANIM["gain"] > 0 and now - XPANIM["gain_t"] < 2.5:
        t.append(f" +{int(XPANIM['gain'])}", style="bold bright_green" if now - XPANIM["gain_t"] < 1.8 else "dim green")
    t.append(f"  {ci()} {coin_state()['bal']:,}", style="bold gold1")
    if CFG["fx"] and COINANIM["gain"] > 0 and now - COINANIM["t"] < 2.5:
        t.append(f" +{COINANIM['gain']}", style="bold bright_yellow" if now - COINANIM["t"] < 1.8 else "dim yellow")
    sl = surge_left()
    if sl > 0:
        t.append(f"  ⚡x{ret_cfg()['surge']['multiplier']:g} {_clock(sl)}", style="bold bright_cyan" if int(now * 2) % 2 else "cyan")
    title = game_title_name()
    if title:
        t.append(f" · {title}", style="bright_white")
    return t

def _until_reset() -> str:
    now = datetime.datetime.now()
    h = GCFG["settings"]["day_rollover_hour"]
    nxt = now.replace(hour=h, minute=0, second=0, microsecond=0)
    if nxt <= now:
        nxt += datetime.timedelta(days=1)
    return fmt_dur((nxt - now).total_seconds())

def _req_text(t) -> str:
    u = t["unlock"]
    if u["type"] == "always":
        return "Available from the start"
    if u["type"] == "level":
        return f"Reach level {u['value']}"
    if u["type"] == "achievement":
        a = GAME["amap"].get(u["id"])
        return f"Achievement: {a['name'] if a else u['id']}"
    if u["type"] == "bounty":
        b = GAME["bmap"].get(u["id"])
        return f"Claim bounty: {b['name'] if b else u['id']}"
    if u["type"] == "quest":
        q = GAME["qmap"].get(u["id"])
        return f"Complete quest: {q['name'] if q else u['id']}"
    return f"{u['metric'].replace('_', ' ')} ≥ {u['target']:g}"

def _fmt_num(x) -> str:
    return f"{x:,.0f}" if float(x) >= 100 or float(x).is_integer() else f"{x:.1f}"

def _page_scroll(rows: list, size, fixed: int):
    """Slice rows for the visible height using the scroll offset; returns (slice, hidden_above, hidden_below)."""
    fit = max(3, size[1] - fixed)
    GAME_UI["scroll"] = max(0, min(GAME_UI["scroll"], max(0, len(rows) - fit)))
    s = GAME_UI["scroll"]
    return rows[s:s + fit], s, max(0, len(rows) - s - fit)

def _profile_page_overview(size) -> Group:
    lvl, into, need = game_progress()
    name, title, rank = STATE["name"], game_title_name(), game_rank(lvl)
    head = Text()
    if SUPPORT["on"]:
        head.append_text(sparkle_text(name, time.time(), glyphs=False))
        head.append("  ")
        head.append_text(sparkle_text("SUPPORTER", time.time()))
    else:
        head.append(f"{name}", style="bold bright_white")
    if title:
        head.append(f"  «{title}»", style="bold cyan")
    if rank:
        head.append(f"   Rank: {rank}", style="magenta")
    bar = Text()
    bar.append(f"Level {lvl}  ", style="bold yellow")
    bar.append_text(mini_bar(into / need if need else 1.0, 24, "yellow"))
    bar.append(f"  {into:,}/{need:,} XP to next" if need else "  MAX LEVEL", style="yellow")
    bar.append(f"   ({STATE['xp']:,} total)", style="dim")
    _m, _mxp = next_streak_milestone(STATE["streak"])
    sub = Text(f"🔥 Streak {STATE['streak']}d 🛡{STATE['shields']} (best {STATE['best_streak']}d, next bonus day {_m}: +{_mxp} XP)   ⭐ This session +{GAME['session_xp']:,} XP   "
               f"⏳ Daily reset in {_until_reset()}", style="dim")
    life = STATE["life"]
    left, right = kv_table(), kv_table()
    for k, v in (("Sessions", life.get("sessions", 0)), ("Devices seen", life.get("devices_seen", 0)),
                 ("Scan time", fmt_dur(life.get("scan_minutes", 0) * 60)), ("Categories", len(STATE["cats"])),
                 ("Vendors", len(STATE["vendors"]))):
        left.add_row(k, Text(f"{v:,}" if isinstance(v, int) else str(v)))
    d = game_day()
    q_done = sum(1 for q in d["quests"] if q in d["done"])
    for k, v in (("Quests today", f"{q_done}/{len([q for q in d['quests'] if q in GAME['qmap']])}"),
                 ("Bounties claimed", f"{life.get('bounties_claimed', 0):,}"),
                 ("Achievements", f"{len(STATE['ach'])}/{len(GCFG['achievements'])}"),
                 ("Titles", f"{len(STATE['titles'])}/{len(GCFG['titles'])}"),
                 ("Hunts won", f"{life.get('hunts_completed', 0):,}"),
                 ("Missions", f"{int(life.get('missions_completed', 0)):,} done · {int(life.get('missions_failed', 0)):,} failed"),
                 ("Intel Coins", f"{ci()} {coin_state()['bal']:,}")):
        right.add_row(k, Text(v))
    stats = Table.grid(expand=True)
    stats.add_column(ratio=1)
    stats.add_column(ratio=1)
    stats.add_row(left, right)
    recent = Table(box=None, show_header=False, expand=True, padding=(0, 1))
    recent.add_column(width=8, style="dim", no_wrap=True)
    recent.add_column(ratio=1, no_wrap=True, overflow="ellipsis")
    for ts, _kind, text in reversed(STATE["log"][-max(3, size[1] - 14):]):
        recent.add_row(datetime.datetime.fromtimestamp(ts).strftime("%H:%M:%S"), Text(str(text)))
    if not STATE["log"]:
        recent.add_row("", Text("Nothing yet. Start scanning to earn XP.", style="dim"))
    return Group(head, bar, sub, Text(""), stats, Text(""), Text("Recent activity", style="bold"), recent)

def _profile_page_quests(size) -> Group:
    d = game_day()
    t = Table(box=ROUNDED, expand=True)
    t.add_column("", width=2, no_wrap=True)
    t.add_column("Quest", ratio=3, overflow="fold")
    t.add_column("Progress", width=30, no_wrap=True)
    t.add_column("Reward", width=8, justify="right", no_wrap=True)
    quests = [GAME["qmap"][q] for q in d["quests"] if q in GAME["qmap"]]
    for q in quests:
        done = q["id"] in d["done"]
        prog = quest_progress(q)
        cell = Text(q["name"], style="green" if done else "bold")
        if q["desc"]:
            cell.append("\n" + q["desc"], style="dim")
        bar = Text()
        bar.append_text(mini_bar(prog / q["target"], 14, "green" if done else "cyan"))
        bar.append(f" {_fmt_num(prog)}/{_fmt_num(q['target'])}", style="dim")
        t.add_row(Text("✓" if done else "○", style="green" if done else "dim"), cell, bar, Text(f"+{q['xp']}", style="yellow"))
    if not quests:
        t.add_row("", Text("No daily quests available (add some to the game config).", style="dim"), "", "")
    foot = Text(f"Resets in {_until_reset()} · {sum(1 for q in quests if q['id'] in d['done'])}/{len(quests)} done · "
                f"streak {STATE['streak']}d (scan {GCFG['settings']['streak_min_scan_minutes']:g}+ min a day to keep it)", style="dim")
    return Group(t, foot, Text(""), cache_status_text())

def _profile_page_bounties(size) -> Group:
    rows = []
    order = list(BOUNTY_DIFF)
    for b in GCFG["bounties"]:
        done, found = bounty_state(b)
        rows.append((done, order.index(b["difficulty"]), b, found))
    rows.sort(key=lambda r: (r[0], r[1]))
    vis, above, below = _page_scroll(rows, size, 9)
    t = Table(box=ROUNDED, expand=True)
    t.add_column("Level", width=7, no_wrap=True)
    t.add_column("Bounty", ratio=3, overflow="fold")
    t.add_column("Found", width=9, justify="center", no_wrap=True)
    t.add_column("Reward", width=8, justify="right", no_wrap=True)
    t.add_column("Status", width=11, no_wrap=True)
    for done, _o, b, found in vis:
        lab, col = BOUNTY_DIFF[b["difficulty"]]
        cell = Text(b["name"], style="green" if done else "bold")
        if b["desc"]:
            cell.append("\n" + b["desc"], style="dim")
        status = Text("✓ claimed" if b["repeat"] == "once" else "✓ today", style="green") if done else \
            Text("open" if b["repeat"] == "once" else "open · daily", style="yellow")
        t.add_row(Text(lab, style=col), cell, Text(f"{min(found, b['count'])}/{b['count']}"), Text(f"+{b['xp']}", style="yellow"), status)
    if not rows:
        t.add_row("", Text("No bounties defined in the game config.", style="dim"), "", "", "")
    n_done = sum(1 for r in rows if r[0])
    more = Text(f"{n_done}/{len(rows)} claimed · ↑/↓ scroll" + (f" · {above} above" if above else "") + (f" · {below} more below" if below else ""), style="dim")
    return Group(t, more)

def _profile_page_achievements(size) -> Group:
    rows = []
    for a in GCFG["achievements"]:
        got = a["id"] in STATE["ach"]
        prog = min(1.0, float(game_metric(a["metric"], "life")) / a["target"])
        rows.append((got, -prog, a, prog))
    rows.sort(key=lambda r: (r[0], r[1]))
    vis, above, below = _page_scroll(rows, size, 9)
    t = Table(box=ROUNDED, expand=True)
    t.add_column("", width=2, no_wrap=True)
    t.add_column("Achievement", ratio=3, overflow="fold")
    t.add_column("Progress", width=26, no_wrap=True)
    t.add_column("Reward", width=8, justify="right", no_wrap=True)
    for got, _p, a, prog in vis:
        hide = a["hidden"] and not got
        cell = Text("???" if hide else a["name"], style="green" if got else "bold")
        cell.append("\n" + ("Hidden achievement: keep exploring." if hide else a["desc"]), style="dim")
        bar = Text()
        if got:
            bar.append("✓ " + datetime.datetime.fromtimestamp(STATE["ach"][a["id"]]).strftime("%Y-%m-%d"), style="green")
        elif hide:
            bar.append("?", style="dim")
        else:
            bar.append_text(mini_bar(prog, 12, "cyan"))
            bar.append(f" {_fmt_num(game_metric(a['metric'], 'life'))}/{_fmt_num(a['target'])}", style="dim")
        t.add_row(Text("🔒" if hide else a["icon"]), cell, bar, Text(f"+{a['xp']}", style="yellow"))
    if not rows:
        t.add_row("", Text("No achievements defined in the game config.", style="dim"), "", "")
    more = Text(f"{len(STATE['ach'])}/{len(rows)} unlocked · ↑/↓ scroll" + (f" · {above} above" if above else "") + (f" · {below} more below" if below else ""), style="dim")
    return Group(t, more)

def _profile_page_titles(size) -> Group:
    rows = sorted(GCFG["titles"], key=lambda t: (t["id"] not in STATE["titles"], 0))
    vis, above, below = _page_scroll(rows, size, 9)
    t = Table(box=ROUNDED, expand=True)
    t.add_column("", width=2, no_wrap=True)
    t.add_column("Title", ratio=2, no_wrap=True, overflow="ellipsis")
    t.add_column("How to unlock", ratio=3, overflow="fold")
    for ti in vis:
        got = ti["id"] in STATE["titles"]
        eq = STATE["title"] == ti["id"]
        mark = Text("★" if eq else "✓" if got else "🔒", style="bold yellow" if eq else "green" if got else "dim")
        how = Text(_req_text(ti), style="dim" if got else "")
        if ti["desc"]:
            how.append("\n" + ti["desc"], style="dim")
        t.add_row(mark, Text(ti["name"], style="bold cyan" if eq else "bold" if got else "dim"), how)
    if not rows:
        t.add_row("", Text("No titles defined in the game config.", style="dim"), "")
    more = Text(f"{len(STATE['titles'])}/{len(GCFG['titles'])} unlocked · ★ equipped · press t to equip a title or rename yourself"
                + (f" · {below} more below (↓)" if below else ""), style="dim")
    return Group(t, more)

def build_profile_panel(size):
    if not GAME["on"]:
        return Panel(Text("The game layer is off (started with --no-game)."), title="Profile", box=ROUNDED)
    page = GAME_UI["page"] % len(GAME_PAGES)
    tabs = Text(no_wrap=True, overflow="ellipsis")
    for n, nm in enumerate(GAME_PAGES):
        tabs.append(f" {nm} ", style="reverse bold" if n == page else "dim")
        tabs.append(" ")
    body = (_profile_page_overview, _profile_page_quests, _profile_page_weekly, _profile_page_bounties,
            _profile_page_achievements, _profile_page_titles, _profile_page_coins, _profile_page_shop)[page](size)
    warn = Text(f"⚠ {len(GAME['warnings'])} config warning(s): run --check-game", style="yellow") if GAME["warnings"] else Text("")
    return Panel(Group(tabs, Text(""), body, warn), title="[bold]🏅 Player Profile[/]", title_align="left",
                 subtitle="←/→ page · ↑/↓ scroll · t title · e coin exchange · p close", border_style="yellow", box=ROUNDED)

def game_profile_key():
    if not GAME["on"]:
        STATUS.set("Game layer is off (started with --no-game).")
        return
    if CFG["show_profile"]:
        GAME_UI["page"] = 0
        toggle_overlay("profile")
    else:
        open_overlay("profile")
        GAME_UI.update(page=0, scroll=0)

def game_profile_nav(ch: str):
    if ch in ("RIGHT", "LEFT"):
        GAME_UI["page"] = (GAME_UI["page"] + (1 if ch == "RIGHT" else -1)) % len(GAME_PAGES)
        GAME_UI["scroll"] = 0
    elif ch in ("DOWN", "j"):
        GAME_UI["scroll"] += 1
    elif ch in ("UP", "k"):
        GAME_UI["scroll"] = max(0, GAME_UI["scroll"] - 1)

# =============================================================================
# MISSION MODE: timed objectives
#
# A mission is a short challenge with a countdown, for example "find 5 different vendors in 3 minutes".
# Press y for the mission board, pick one by its number and the clock starts. The countdown runs along the top of
# every view and only ticks while scanning is on. Finish in time and it pays XP and Intel Coins; run out of time and
# nothing is lost. Missions also feed the metrics missions_started / missions_completed / missions_failed, so daily
# quests, achievements and titles can be built on them.
#
# All missions live in lookout_game.json under "missions" (edit it while the scanner runs). Objectives are either
#   {"distinct": "vendor", "target": 5}                      count different vendors / categories / labels / manufacturers
#   {"match": {...bounty-style rule...}, "target": 2}          count devices that match a rule (add "distinct" to count unique values)
#   {"metric": "rotations_linked", "target": 3}                count how much a counter grows during the mission
# By default only devices that are NEW since the clock started count ("scope": "new"); "scope": "any" counts anything in range.
# =============================================================================
MISSION_KEY = "y"
MISSION_COUNTER_METRICS = ("devices_seen", "packets", "alerts_found", "possibles_found", "followers_flagged",
                           "hunts_started", "hunts_completed", "rotations_linked", "devices_renamed")
MISSION_COUNTER_PREFIXES = ("category:", "tier:", "vendor:", "addr:")
MISSION_DISTINCT = {"vendor": "vendors", "category": "categories", "label": "device types", "manufacturer": "manufacturers"}
MISSION_REPEAT = {"daily": "pays once a day", "once": "pays once, ever", "unlimited": "pays every time"}
MISSION_SCOPES = ("new", "any")
MISSION_DEFAULT_XP = {"easy": 40, "medium": 90, "hard": 180, "elite": 350}
MISSION_SPEED_FRAC = 0.5          # finish with at least this share of the clock left for the speed bonus
MISSION_SPEED_XP = 0.25           # ... which adds this share of the mission's XP (plus coin_rules.mission_speed_bonus coins)
MISSION_TICK_SECONDS = 10         # in the last N seconds, mission_tick.(wav|mp3|ogg|flac) plays once a second if the file exists
MISSION_PER_PAGE = 9
MISSION = {"active": None, "last_eval": 0.0, "abandon_at": 0.0, "flash_until": 0.0, "last_sec": -1}
MISSION_UI = {"page": 0, "per": MISSION_PER_PAGE}

# ---------------------------------------------------------------- config parsing
def _mission_objective(raw, label: str, warns: list):
    """One objective of a mission -> dict, or None (with a warning) if it is unusable."""
    if not isinstance(raw, dict):
        warns.append(f"{label}: an objective is not an object; mission skipped")
        return None
    target = _gnum(raw.get("target"), 0, 0)
    if target <= 0:
        warns.append(f"{label}: every objective needs a 'target' above 0; mission skipped")
        return None
    o = {"target": int(max(1, min(5000, round(target)))), "metric": "", "rule": {}, "distinct": "",
         "label": clean(raw.get("label", ""), 40)}
    metric = str(raw.get("metric", "")).strip().lower()
    if metric:
        ok = metric in MISSION_COUNTER_METRICS or any(metric.startswith(p) and len(metric) > len(p) for p in MISSION_COUNTER_PREFIXES)
        if not ok:
            warns.append(f"{label}: metric '{metric}' can't be used in a mission (counters only: {', '.join(MISSION_COUNTER_METRICS)}, "
                         f"category:<x>, tier:<x>, vendor:<x>, addr:<x>); mission skipped")
            return None
        o["metric"] = metric
        o["label"] = o["label"] or metric.replace("category:", "").replace("tier:", "").replace("addr:", "").replace("_", " ")
        return o
    dist = str(raw.get("distinct", "")).strip().lower()
    if dist:
        if dist not in MISSION_DISTINCT:
            warns.append(f"{label}: distinct '{dist}' unknown (use {', '.join(MISSION_DISTINCT)}); mission skipped")
            return None
        o["distinct"] = dist
    if raw.get("match") is not None:
        rule = compile_match(raw["match"], label, warns)
        if rule is None:
            return None
        o["rule"] = rule
    o["label"] = o["label"] or (f"different {MISSION_DISTINCT[dist]}" if dist else "devices")
    return o

def parse_missions(raw_list, warns: list) -> list:
    """The 'missions' list of the game config. Bad entries are skipped with a warning; never raises."""
    out, seen = [], set()
    for raw in _glist(raw_list):
        if not isinstance(raw, dict):
            warns.append("missions: entry is not an object; skipped")
            continue
        mid = _gid(raw.get("id"), "mission", seen, warns)
        if not mid:
            continue
        label = f"mission '{mid}'"
        raws = raw.get("objectives")
        if raws is None and any(k in raw for k in ("metric", "match", "distinct", "target")):
            raws = [raw]                                    # shorthand: a single objective written at the top level
        raws = _glist(raws)
        if not raws:
            warns.append(f"{label}: needs an 'objectives' list; skipped")
            continue
        if len(raws) > 4:
            warns.append(f"{label}: more than 4 objectives; only the first 4 are used")
        objs = []
        for r in raws[:4]:
            o = _mission_objective(r, label, warns)
            if o is None:
                objs = []
                break
            objs.append(o)
        if not objs:
            continue
        diff = str(raw.get("difficulty", "medium")).lower()
        if diff not in BOUNTY_DIFF:
            warns.append(f"{label}: difficulty '{diff}' unknown (easy/medium/hard/elite); using medium")
            diff = "medium"
        rep = str(raw.get("repeat", "daily")).lower()
        if rep not in MISSION_REPEAT:
            warns.append(f"{label}: repeat '{rep}' unknown ({'/'.join(MISSION_REPEAT)}); using daily")
            rep = "daily"
        scope = str(raw.get("scope", "new")).lower()
        if scope not in MISSION_SCOPES:
            warns.append(f"{label}: scope '{scope}' unknown (new/any); using new")
            scope = "new"
        secs = raw.get("time")
        if secs is None and raw.get("minutes") is not None:
            secs = _gnum(raw.get("minutes"), 3, 0.25, 120) * 60
        out.append({"id": mid, "name": clean(raw.get("name") or mid, 40), "desc": clean(raw.get("description", ""), 140),
                    "time": int(_gnum(secs, 180, 15, 7200)), "difficulty": diff, "repeat": rep, "scope": scope,
                    "xp": int(_gnum(raw.get("xp"), MISSION_DEFAULT_XP[diff], 0, 1e6)),
                    "min_level": int(_gnum(raw.get("min_level"), 1, 1, 1000)), "coins": _opt_coins(raw), "objs": objs})
    return out

def parse_boot(raw) -> dict:
    """The 'boot' block of the game config (startup sequence settings)."""
    b = dict(GAME_DEFAULT_BOOT)
    if isinstance(raw, dict):
        b["enabled"] = bool(raw.get("enabled", True))
        b["speed"] = _gnum(raw.get("speed"), 1.0, 0.25, 4.0)
        b["banner"] = clean(raw.get("banner", b["banner"]), 24).upper() or b["banner"]
        b["play_intro"] = bool(raw.get("play_intro", True))
        b["lines"] = [x for x in (clean(v, 70) for v in _glist(raw.get("lines"))) if x][:6]
    return b

# ---------------------------------------------------------------- state
def mission_state() -> dict:
    """Lifetime mission records inside the profile: completions per mission and the best (fastest) time of each."""
    m = STATE.get("missions")
    if not isinstance(m, dict):
        m = STATE["missions"] = {}
    for k in ("done", "best"):
        if not isinstance(m.get(k), dict):
            m[k] = {}
    return m

def mission_day() -> dict:
    """Today's mission record: which missions already paid out."""
    d = game_day()
    md = d.get("missions")
    if not isinstance(md, dict):
        md = d["missions"] = {}
    if not isinstance(md.get("paid"), list):
        md["paid"] = []
    return md

def mission_paid(m) -> bool:
    """True when this mission has already paid its reward for its repeat period (it can still be played for fun)."""
    if m["repeat"] == "unlimited":
        return False
    if m["repeat"] == "once":
        return mission_state()["done"].get(m["id"], 0) > 0
    return m["id"] in mission_day()["paid"]

def mission_coins(m) -> int:
    if m.get("coins") is not None:
        return m["coins"]
    return GCFG["coin_rules"].get(f"mission_{m['difficulty']}", 0)

def mission_board() -> list:
    """Every mission, available ones first, easiest first."""
    lvl, order = game_level(), list(BOUNTY_DIFF)
    return sorted(GCFG.get("missions", []), key=lambda m: (m["min_level"] > lvl, order.index(m["difficulty"]), m["time"], m["name"]))

def mission_goal_text(m) -> str:
    return " + ".join(f"{o['target']} {o['label']}" for o in m["objs"])

def _mmss(sec: float) -> str:
    s = max(0, int(math.ceil(sec)))
    return f"{s // 60:02d}:{s % 60:02d}"

def mission_left(a) -> float:
    return max(0.0, a["m"]["time"] - a["elapsed"])

# ---------------------------------------------------------------- running a mission
def _fresh_objectives(m) -> list:
    return [{"o": o, "keys": set(), "n": 0,
             "base": float(game_metric(o["metric"], "life")) if o["metric"] else 0.0} for o in m["objs"]]

def mission_start(mid: str) -> str:
    if not GAME["on"]:
        return "Game layer is off (started with --no-game)."
    if MISSION["active"]:
        return "A mission is already running. Press 0 on the mission board (y) to abandon it first."
    m = GAME["mimap"].get(mid)
    if m is None:
        return "That mission doesn't exist any more."
    lvl = game_level()
    if lvl < m["min_level"]:
        return f"{m['name']} unlocks at level {m['min_level']} (you are level {lvl})."
    now = time.time()
    MISSION["active"] = {"m": m, "t0": now, "elapsed": 0.0, "objs": _fresh_objectives(m),
                         "pre": {d.ghost_id or d.mac for d in DEVICES.values()}}      # devices already known don't count as new
    MISSION.update(flash_until=now + 2.0, last_sec=-1, last_eval=0.0)
    game_bump("missions_started")
    game_note(f"🎯 MISSION STARTED: {m['name']}: {mission_goal_text(m)} in {fmt_dur(m['time'])}", "mission", False)
    play_notification_sound("mission_start")
    return f"Mission started: {m['name']}. {mission_goal_text(m)} in {fmt_dur(m['time'])}. Go!"

def mission_abandon() -> str:
    a = MISSION["active"]
    if not a:
        return "No mission is running."
    MISSION["active"] = None
    game_note(f"🏳 Mission abandoned: {a['m']['name']}", "mission", False)
    return f"Abandoned {a['m']['name']}. No penalty."

def _distinct_values(dev, kind: str) -> list:
    i = dev.ident
    if kind == "vendor":
        return [norm(clean(i.vendor, 40))] if i.vendor else []
    if kind == "category":
        return [i.category] if i.category else []
    if kind == "label":
        return [norm(clean(i.label, 40))] if i.label else []
    return [f"{x:#06x}" for x in dev.mfg_ids]                       # manufacturer: SIG company ids

def mission_eval(a, now: float):
    """Refresh every objective's progress from what the scanner is hearing right now."""
    m = a["m"]
    live = [d for d in DEVICES.values() if d.counted and now - d.last <= ACTIVE_WINDOW]
    if m["scope"] == "new":
        live = [d for d in live if (d.ghost_id or d.mac) not in a["pre"]]
    for st in a["objs"]:
        o = st["o"]
        if o["metric"]:
            st["n"] = max(0, int(game_metric(o["metric"], "life") - st["base"]))
            continue
        for d in live:
            if o["rule"] and not bounty_matches(o["rule"], d):
                continue
            if o["distinct"]:
                st["keys"].update(v for v in _distinct_values(d, o["distinct"]) if v)
            else:
                st["keys"].add(d.ghost_id or d.mac)
        st["n"] = len(st["keys"])

def mission_done(a) -> bool:
    return all(st["n"] >= st["o"]["target"] for st in a["objs"])

def mission_finish(ok: bool):
    a = MISSION["active"]
    MISSION["active"] = None
    if not a:
        return
    m, took, left = a["m"], a["elapsed"], mission_left(a)
    if not ok:
        game_bump("missions_failed")
        got = " · ".join(f"{min(st['n'], st['o']['target'])}/{st['o']['target']} {st['o']['label']}" for st in a["objs"])
        game_note(f"⏱ MISSION FAILED: {m['name']} (time ran out: {got})", "mission", False)
        game_fx("mission_fail", m["name"], got, "Press y to try again")
        return
    ms = mission_state()
    paid_before = mission_paid(m)                        # check before recording this run
    game_bump("missions_completed")
    ms["done"][m["id"]] = ms["done"].get(m["id"], 0) + 1
    if m["id"] not in ms["best"] or took < ms["best"][m["id"]]:
        ms["best"][m["id"]] = round(took, 1)
    xp = cn = 0
    fast = left >= m["time"] * MISSION_SPEED_FRAC
    if not paid_before:
        if m["repeat"] == "daily":
            mission_day()["paid"].append(m["id"])
        xp = m["xp"] + (round(m["xp"] * MISSION_SPEED_XP) if fast else 0)
        game_grant(xp, f"mission {m['id']}")
        extra = GCFG["coin_rules"].get("mission_speed_bonus", 0) if fast else 0
        cn = coins_grant(mission_coins(m) + extra, f"mission {m['id']}", "mission_reward")
    detail = f"{fmt_dur(took)} of {fmt_dur(m['time'])}" + (" · speed bonus" if fast and not paid_before else "")
    game_note(f"🎯 MISSION COMPLETE: {m['name']} in {fmt_dur(took)}" +
              (f" (+{xp} XP" + (f", +{cn} {ci()}" if cn else "") + ")" if not paid_before else " (already paid today)"), "mission", False)
    reward = reward_text(xp, cn) if not paid_before else {"daily": "Reward already paid today", "once": "Reward already paid"}.get(m["repeat"], "")
    game_fx("mission", m["name"], detail, reward)

def mission_tick(now: float, dt: float):
    """Called every UI tick: advances the clock (only while scanning), checks objectives, ends the mission."""
    a = MISSION["active"]
    if not a or not GAME["on"]:
        return
    if dt > 0:
        a["elapsed"] += dt
    if now - MISSION["last_eval"] >= 0.5:
        MISSION["last_eval"] = now
        mission_eval(a, now)
        if mission_done(a):
            return mission_finish(True)
    left = mission_left(a)
    if left <= 0:
        mission_eval(a, now)                              # one last look so a last-second find still counts
        return mission_finish(mission_done(a))
    sec = int(math.ceil(left))
    if sec <= MISSION_TICK_SECONDS and sec != MISSION["last_sec"]:
        MISSION["last_sec"] = sec
        if find_sound("mission_tick"):
            play_notification_sound("mission_tick")

# ---------------------------------------------------------------- display
def _mission_clock_style(left: float, total: float, now: float) -> str:
    if left <= MISSION_TICK_SECONDS:
        return "bold bright_red" if int(now * 2) % 2 == 0 else "bold red"
    frac = left / total if total else 0.0
    return "bold red" if frac <= 0.25 else "bold yellow" if frac <= 0.5 else "bold bright_green"

def mission_objective_rows(a, bar_w: int = 16) -> list:
    rows = []
    for st in a["objs"]:
        o = st["o"]
        n = min(st["n"], o["target"])
        frac = n / o["target"]
        t = Text(no_wrap=True, overflow="ellipsis")
        t.append("✓ " if frac >= 1 else "○ ", style="green" if frac >= 1 else "dim")
        t.append_text(mini_bar(frac, bar_w, "green" if frac >= 1 else "cyan"))
        t.append(f" {n}/{o['target']} ", style="bold green" if frac >= 1 else "bold")
        t.append(o["label"])
        rows.append(t)
    return rows

def mission_strip_text(now: float):
    """HUD row shown while a mission is running: name, countdown, and each objective's progress. None when idle."""
    a = MISSION["active"]
    if not a:
        return None
    m, left = a["m"], mission_left(a)
    style = _mission_clock_style(left, m["time"], now)
    t = Text(no_wrap=True, overflow="ellipsis")
    t.append("🎯 MISSION ", style="bold reverse bright_cyan" if now < MISSION["flash_until"] else "bold bright_cyan")
    t.append(f"{clean(m['name'], 26)} ", style="bold bright_white")
    t.append(f"⏱ {_mmss(left)} ", style=style)
    if not CFG["scanning"]:
        t.append("⏸ paused ", style="bold yellow")
    t.append_text(mini_bar(left / m["time"] if m["time"] else 0.0, 8, "red" if left <= MISSION_TICK_SECONDS else "yellow" if left / m["time"] <= 0.5 else "green"))
    for st in a["objs"]:
        o = st["o"]
        n = min(st["n"], o["target"])
        t.append("  ·  ", style="dim")
        t.append(f"{n}/{o['target']} {clean(o['label'], 22)}", style="bold green" if n >= o["target"] else "bright_white")
    return t

def mission_status(m):
    """(kind, label) for a board row: 'locked', 'paid' or 'go'."""
    if game_level() < m["min_level"]:
        return "locked", f"🔒 level {m['min_level']}"
    if mission_paid(m):
        return "paid", "✓ done" if m["repeat"] == "once" else "✓ paid today"
    return "go", "▶ start"

def build_missions_panel(size):
    if not GAME["on"]:
        return Panel(Text("The game layer is off (started with --no-game)."), title="Missions", box=ROUNDED)
    W, H = size
    now = time.time()
    a = MISSION["active"]
    life, day = STATE["life"], game_day()["c"]
    head = Text()
    head.append("🎯 MISSION BOARD  ", style="bold bright_cyan")
    head.append(f"{int(day.get('missions_completed', 0))} completed today · {int(life.get('missions_completed', 0))} total · "
                f"{int(life.get('missions_failed', 0))} failed", style="dim")
    parts = [head, Text("")]
    if a:
        m, left = a["m"], mission_left(a)
        style = _mission_clock_style(left, m["time"], now)
        title = Text(no_wrap=True, overflow="ellipsis")
        title.append("ACTIVE  ", style="bold bright_cyan")
        title.append(m["name"], style="bold bright_white")
        if m["desc"]:
            title.append("  " + m["desc"], style="dim")
        parts.append(title)
        big = fx_big(_mmss(left), max(10, W - 12), 5) if H >= 30 else None
        if big:
            parts += [Align.center(Text(r, style=style, no_wrap=True)) for r in big]
        else:
            parts.append(Align.center(Text(f"⏱  {_mmss(left)}", style=style)))
        if not CFG["scanning"]:
            parts.append(Align.center(Text("⏸ scanning is paused, so the clock is paused too", style="bold yellow")))
        parts += mission_objective_rows(a, bar_w=max(10, min(30, W - 50)))
        parts.append(Text(""))
    used = len(parts) + ((len(big) - 1) if a and big else 0)
    board = mission_board()
    per = max(2, min(MISSION_PER_PAGE, (H - used - 9) // 2))
    MISSION_UI["per"] = per
    pages = max(1, math.ceil(len(board) / per))
    MISSION_UI["page"] = max(0, min(MISSION_UI["page"], pages - 1))
    page = board[MISSION_UI["page"] * per:(MISSION_UI["page"] + 1) * per]
    t = Table(box=ROUNDED, expand=True)
    t.add_column("#", width=2, justify="right", style="bold yellow", no_wrap=True)
    t.add_column("Level", width=7, no_wrap=True)
    t.add_column("Mission", ratio=3, overflow="fold")
    t.add_column("Clock", width=7, justify="right", no_wrap=True)
    t.add_column("Reward", width=15, justify="right", no_wrap=True)
    t.add_column("Status", width=13, no_wrap=True)
    best = mission_state()["best"]
    for n, m in enumerate(page, 1):
        lab, col = BOUNTY_DIFF[m["difficulty"]]
        kind, status = mission_status(m)
        cell = Text(m["name"], style="dim" if kind == "locked" else "bold")
        cell.append("\n" + mission_goal_text(m), style="dim")
        if m["id"] in best:
            cell.append(f"  (best {fmt_dur(best[m['id']], True)})", style="dim green")
        reward = Text(f"+{m['xp']} XP", style="yellow")
        if mission_coins(m):
            reward.append(f"  +{mission_coins(m)} {ci()}", style="gold1")
        t.add_row(str(n), Text(lab, style=col), cell, Text(fmt_dur(m["time"], True)), reward,
                  Text(status, style={"go": "bold yellow", "paid": "green", "locked": "dim"}[kind]))
    if not board:
        t.add_row("", "", Text("No missions yet: add some under \"missions\" in the game config.", style="dim"), "", "", "")
    parts.append(t)
    foot = Text("Only devices heard for the first time after the clock starts count (unless a mission says otherwise). "
                "The clock only runs while scanning.", style="dim")
    parts.append(foot)
    sub = f"1-{max(1, len(page))} start · 0 abandon · " + ("←/→ page · " if pages > 1 else "") + "y close"
    return Panel(Group(*parts), title="[bold]🎯 Missions[/]", title_align="left", subtitle=sub,
                 border_style="bright_cyan", box=ROUNDED)

def mission_key():
    if not GAME["on"]:
        STATUS.set("Game layer is off (started with --no-game).")
        return
    if CFG["show_missions"]:
        toggle_overlay("missions")
    else:
        open_overlay("missions")
        MISSION_UI["page"] = 0

def mission_nav(ch: str) -> str:
    """Keys while the mission board is open. Returns a status-line message ('' for none)."""
    board = mission_board()
    per = MISSION_UI["per"]
    pages = max(1, math.ceil(len(board) / per))
    if ch in ("RIGHT", "LEFT"):
        MISSION_UI["page"] = (MISSION_UI["page"] + (1 if ch == "RIGHT" else -1)) % pages
        return ""
    if ch == "0":
        a = MISSION["active"]
        if not a:
            return "No mission is running."
        now = time.time()
        if now - MISSION["abandon_at"] > 4.0:
            MISSION["abandon_at"] = now
            return f"Press 0 again within 4 seconds to abandon '{a['m']['name']}'."
        MISSION["abandon_at"] = 0.0
        return mission_abandon()
    if len(ch) == 1 and ch.isdigit():
        idx = MISSION_UI["page"] * per + int(ch) - 1
        if int(ch) > per or idx >= len(board):
            return "Pick a mission number from the list."
        msg = mission_start(board[idx]["id"])
        if MISSION["active"]:
            close_overlays()                              # back to the scanner: the countdown is in the top bar
        return msg
    return ""

# =============================================================================
# INTEL COINS: the second currency
#
# Earned by playing (quests, bounties, achievements, level-ups, streak milestones, tactical finds, hunts, new categories,
# scan time, new-device batches) and spent in the Coin Exchange (key e) on hacker interface themes, neon mode, glitch
# effects and a few terminal extras. Rates, daily caps, prices and levels all live in lookout_game.json
# ("coin_rules", "coin_caps", "settings", "shop"), so you can retune the economy while the scanner runs.
# Purchases and the equipped set are saved in lookout_profile.json under "coins".
# =============================================================================
COINANIM = {"gain": 0, "t": -99.0}            # the '+N' tag next to the balance in the HUD

def ci() -> str:
    """The coin icon (settings.coin_icon in the game config)."""
    return GCFG.get("settings", {}).get("coin_icon") or GAME_DEFAULT_SETTINGS["coin_icon"]

def coin_state() -> dict:
    c = STATE.get("coins")
    if not isinstance(c, dict):
        c = STATE["coins"] = {}
    for k in ("bal", "earned", "spent"):
        v = c.get(k)
        c[k] = max(0, int(v)) if isinstance(v, (int, float)) and v == v else 0
    if not isinstance(c.get("owned"), dict):
        c["owned"] = {}
    eq = c.get("equipped")
    c["equipped"] = {s: (eq.get(s, "") if isinstance(eq, dict) and isinstance(eq.get(s, ""), str) else "") for s in COSMETIC_SLOTS}
    if not isinstance(c.get("log"), list):
        c["log"] = []
    return c

def coins_grant(amount, why: str = "", event=None) -> int:
    """Pay Intel Coins and return what was actually paid. `event` applies that event's daily cap (coin_caps)."""
    if not GAME["on"]:
        return 0
    amt = int(amount)
    if amt <= 0:
        return 0
    c = coin_state()
    if event:
        cap = GCFG["coin_caps"].get(event)
        if cap is not None:
            d = game_day()
            by = d.setdefault("coin_by", {})
            used = by.get(event, 0)
            amt = min(amt, max(0, cap - used))
            if amt <= 0:
                capped = d.setdefault("coin_capped", [])
                if event not in capped:                    # say so once a day instead of silently paying nothing
                    capped.append(event)
                    game_note(f"⛔ Daily {ci()} cap reached for '{event}' ({cap}/day). It resets in {_until_reset()}.", "info", True)
                return 0
            by[event] = used + amt
    now = time.time()
    c["bal"] += amt
    c["earned"] += amt
    GAME["session_coins"] += amt
    COINANIM["gain"] = (COINANIM["gain"] if now - COINANIM["t"] < 2.5 else 0) + amt
    COINANIM["t"] = now
    c["log"].append([now, amt, why])
    del c["log"][:-30]
    GAME["dirty"] = True
    return amt

def coins_for(event: str, mult: int = 1) -> int:
    """Coins for a gameplay event, using the config's rate and daily cap."""
    return coins_grant(GCFG["coin_rules"].get(event, 0) * mult, event, event) if GAME["on"] else 0

def quest_coins(q) -> int:
    if q.get("coins") is not None:
        return q["coins"]
    return max(1, round(q["xp"] / GCFG["settings"]["quest_xp_per_coin"])) if q["xp"] > 0 else 0

def achievement_coins(a) -> int:
    if a.get("coins") is not None:
        return a["coins"]
    return max(1, round(a["xp"] / GCFG["settings"]["achievement_xp_per_coin"])) if a["xp"] > 0 else 0

def bounty_coins(b) -> int:
    if b.get("coins") is not None:
        return b["coins"]
    return GCFG["coin_rules"].get(f"bounty_{b['difficulty']}", 0)

def reward_text(xp: int, coins: int = 0) -> str:
    return f"+{xp} XP" + (f" · +{coins} {ci()}" if coins else "")

# ---------------------------------------------------------------- the shop
def shop_items(include_hidden: bool = False) -> list:
    owned = coin_state()["owned"]
    order = list(SHOP_TYPES)
    items = [it for it in GCFG["shop"] if include_hidden or not it["hidden"] or it["id"] in owned]
    return sorted(items, key=lambda it: (order.index(it["type"]), it["price"], it["name"]))

def shop_status(it) -> str:
    """'equipped', 'owned', 'locked' (level too low), 'poor' (can't afford yet), 'maxed' (consumable already at its limit) or 'buy'."""
    c = coin_state()
    if it["type"] == "boost":
        if STATE.get("shields", 0) >= shield_max():
            return "maxed"
        if game_level() < it["min_level"]:
            return "locked"
        return "poor" if c["bal"] < it["price"] else "buy"
    if it["id"] in c["owned"]:
        return "equipped" if c["equipped"].get(it["type"]) == it["id"] else "owned"
    if game_level() < it["min_level"]:
        return "locked"
    return "poor" if c["bal"] < it["price"] else "buy"

def shop_buy_boost(it) -> str:
    """Consumables (the Streak Shield) can be bought again and again, up to the carry limit."""
    c = coin_state()
    if STATE["shields"] >= shield_max():
        return f"You already hold the maximum of {shield_max()} Streak Shield(s)."
    lvl = game_level()
    if lvl < it["min_level"]:
        return f"{it['name']} unlocks at level {it['min_level']} (you are level {lvl})."
    if c["bal"] < it["price"]:
        return f"Not enough Intel Coins: {it['name']} costs {it['price']:,}, you have {c['bal']:,}."
    now = time.time()
    c["bal"] -= it["price"]
    c["spent"] += it["price"]
    STATE["shields"] += 1
    c["log"].append([now, -it["price"], f"bought {it['name']}"])
    del c["log"][:-30]
    GAME["dirty"] = True
    game_save(force=True)
    game_note(f"🛡 Bought a Streak Shield (-{it['price']:,}). You hold {STATE['shields']}/{shield_max()}.", "shop", False)
    return f"Bought a Streak Shield: you hold {STATE['shields']}/{shield_max()}. Balance: {c['bal']:,} {ci()}"

def shop_buy(it) -> str:
    if it["type"] == "boost":
        return shop_buy_boost(it)
    c = coin_state()
    if it["id"] in c["owned"]:
        return f"You already own {it['name']}."
    lvl = game_level()
    if lvl < it["min_level"]:
        return f"{it['name']} unlocks at level {it['min_level']} (you are level {lvl})."
    if c["bal"] < it["price"]:
        return f"Not enough Intel Coins: {it['name']} costs {it['price']:,}, you have {c['bal']:,}."
    now = time.time()
    c["bal"] -= it["price"]
    c["spent"] += it["price"]
    c["owned"][it["id"]] = now
    c["equipped"][it["type"]] = it["id"]                   # buying equips: that's what you wanted to see
    c["log"].append([now, -it["price"], f"bought {it['name']}"])
    del c["log"][:-30]
    GAME["dirty"] = True
    game_save(force=True)
    game_note(f"{ci()} Unlocked {it['name']} (-{it['price']:,}). Balance {c['bal']:,}", "shop", False)
    game_fx("shop", it["name"], SHOP_TYPES[it["type"]], f"-{it['price']:,} {ci()} · equipped")
    return f"Unlocked and equipped {it['name']}. Balance: {c['bal']:,} {ci()}"

def shop_equip(it) -> str:
    """Equip an owned item; doing it again on the equipped one takes it off."""
    c = coin_state()
    if it["id"] not in c["owned"]:
        return f"You don't own {it['name']} yet."
    if c["equipped"].get(it["type"]) == it["id"]:
        c["equipped"][it["type"]] = ""
        msg = f"Took off {it['name']}."
    else:
        c["equipped"][it["type"]] = it["id"]
        msg = f"Equipped {it['name']}."
    GAME["dirty"] = True
    game_save(force=True)
    return msg

def shop_flow() -> str:
    """The Coin Exchange: buy, equip / unequip and preview. Returns a status-line message."""
    if not GAME["on"]:
        return "Game layer is off (started with --no-game)."
    console = Console()
    msg = ""
    while True:
        c = coin_state()
        items = shop_items()
        sys.stdout.write("\033[H\033[J")
        table = Table(title=Text(f"{ci()} Intel Coin Exchange · balance {c['bal']:,} {ci()}"), box=ROUNDED, expand=False)
        table.add_column("#", justify="right", style="bold yellow")
        table.add_column("Item", no_wrap=True)
        table.add_column("Type", style="dim", no_wrap=True)
        table.add_column("Price", justify="right", no_wrap=True)
        table.add_column("Status", no_wrap=True)
        table.add_column("What it does", overflow="fold", max_width=54)
        for n, it in enumerate(items, 1):
            st = shop_status(it)
            label = {"equipped": Text("★ equipped", style="bold green"), "owned": Text("✓ owned", style="green"),
                     "locked": Text(f"🔒 level {it['min_level']}", style="dim"),
                     "poor": Text("need more", style="red"), "buy": Text("buy", style="bold yellow"),
                     "maxed": Text("full", style="dim")}[st]
            price_style = "dim" if st in ("equipped", "owned") else "red" if st == "poor" else "yellow"
            table.add_row(str(n), Text(it["name"] + (f"  (holding {STATE['shields']}/{shield_max()})" if it["type"] == "boost" else ""),
                                       style="bold" if st in ("equipped", "owned") else ""),
                          Text(SHOP_TYPES[it["type"]]),
                          Text(f"{it['price']:,}" if st not in ("equipped", "owned") else "—", style=price_style), label, Text(it["desc"], style="dim"))
        if not items:
            console.print(Text("The exchange is empty (nothing defined under \"shop\" in the game config).", style="dim"))
        else:
            console.print(table)
        slots = "   ".join(f"{s}: {GAME['smap'][c['equipped'][s]]['name'] if c['equipped'][s] in GAME['smap'] else 'off'}" for s in COSMETIC_SLOTS)
        console.print(Text(f"Equipped  {slots}", style="dim"))
        console.print(Text("Type a number to buy it, or to equip / take off something you own.   pN = preview item N for "
                           f"{PREVIEW_SECONDS:.0f}s   blank = leave", style="dim"))
        if msg:
            console.print(Text(msg, style="bold yellow"))
        choice = ask("> ").strip().lower()
        if not choice:
            return msg or "Left the Coin Exchange."
        prev = choice.startswith("p")
        idx = parse_index(choice[1:].strip() if prev else choice, len(items))
        if not idx:
            msg = "Type an item number from the list (or pN to preview)."
            continue
        it = items[idx - 1]
        if it["type"] == "boost":
            msg = "A Streak Shield is used automatically, so there is nothing to preview." if prev else shop_buy_boost(it)
            continue
        if prev:
            PREVIEW.update(item=it["id"], until=time.time() + PREVIEW_SECONDS)
            return f"Previewing {it['name']} for {PREVIEW_SECONDS:.0f}s. Press e to buy it or equip it."
        if it["id"] in c["owned"]:
            msg = shop_equip(it)
        else:
            msg = shop_buy(it)
            if c["owned"].get(it["id"]):                   # bought: the celebration card plays when we return to the dashboard
                return msg

# ---------------------------------------------------------------- profile pages
def _profile_page_coins(size) -> Group:
    c = coin_state()
    head = Text()
    head.append(f"{ci()} {c['bal']:,} Intel Coins", style="bold gold1")
    head.append(f"   earned {c['earned']:,} · spent {c['spent']:,} · this session +{GAME['session_coins']:,}", style="dim")
    st, r, caps = GCFG["settings"], GCFG["coin_rules"], GCFG["coin_caps"]
    earn = Table(box=ROUNDED, expand=True)
    earn.add_column("Earn coins by", ratio=3, overflow="fold")
    earn.add_column("Pays", width=14, justify="right", no_wrap=True)
    earn.add_column("Daily cap", width=9, justify="right", no_wrap=True)
    rows = [("Completing a daily quest", f"≈ XP ÷ {st['quest_xp_per_coin']:g}", ""),
            ("Finishing all of today's quests", r.get("all_quests_done", 0), ""),
            ("Claiming a bounty (easy / medium / hard / elite)",
             "/".join(str(r.get(f"bounty_{d}", 0)) for d in BOUNTY_DIFF), ""),
            ("Completing a mission (easy / medium / hard / elite)",
             "/".join(str(r.get(f"mission_{d}", 0)) for d in BOUNTY_DIFF), caps.get("mission_reward", "")),
            ("Finishing a mission with half the clock left", f"+{r.get('mission_speed_bonus', 0)}", ""),
            ("Unlocking an achievement", f"≈ XP ÷ {st['achievement_xp_per_coin']:g}", ""),
            ("Reaching a new level", r.get("level_up", 0), ""),
            ("A streak milestone", f"≈ XP ÷ {st['streak_xp_per_coin']:g}", "")]
    for ev, desc in GAME_COIN_EVENTS.items():
        if ev in ("all_quests_done", "level_up") or ev.startswith(("bounty_", "mission_")):
            continue
        label = desc[0].upper() + desc[1:]
        if ev == "device_batch":
            label = f"Every {st['devices_per_coin']:g} new devices"
        rows.append((label, r.get(ev, 0), caps.get(ev, "")))
    for label, pays, cap in rows:
        earn.add_row(Text(label), Text(str(pays), style="gold1"), Text(str(cap), style="dim"))
    equipped = Text()
    for s in COSMETIC_SLOTS:
        it = GAME["smap"].get(c["equipped"].get(s, ""))
        equipped.append(f"{s}: ", style="dim")
        equipped.append((it["name"] if it else "off") + "   ", style="bold" if it else "dim")
    recent = Table(box=None, show_header=False, expand=True, padding=(0, 1))
    recent.add_column(width=8, style="dim", no_wrap=True)
    recent.add_column(width=8, justify="right", no_wrap=True)
    recent.add_column(ratio=1, no_wrap=True, overflow="ellipsis")
    for ts, amt, why in reversed(c["log"][-6:]):
        recent.add_row(datetime.datetime.fromtimestamp(ts).strftime("%H:%M:%S"),
                       Text(f"{amt:+,}", style="green" if amt > 0 else "red"), Text(str(why)))
    if not c["log"]:
        recent.add_row("", "", Text("No coins yet. Finish a quest or claim a bounty.", style="dim"))
    hint = Text("Press e to open the Coin Exchange and spend them.", style="bold yellow")
    return Group(head, Text(""), earn, Text(""), equipped, Text(""), Text("Recent coin activity", style="bold"), recent, Text(""), hint)

def _profile_page_shop(size) -> Group:
    items = shop_items()
    vis, above, below = _page_scroll(items, size, 9)
    t = Table(box=ROUNDED, expand=True)
    t.add_column("", width=2, no_wrap=True)
    t.add_column("Item", ratio=2, no_wrap=True, overflow="ellipsis")
    t.add_column("What it does", ratio=4, overflow="fold")
    t.add_column("Price", width=8, justify="right", no_wrap=True)
    t.add_column("Status", width=12, no_wrap=True)
    for it in vis:
        st = shop_status(it)
        mark = Text({"equipped": "★", "owned": "✓", "locked": "🔒", "poor": "○", "buy": "●", "maxed": "✓"}[st],
                    style="bold yellow" if st == "equipped" else "green" if st == "owned" else "dim")
        status = {"equipped": Text("equipped", style="bold green"), "owned": Text("owned", style="green"),
                  "locked": Text(f"level {it['min_level']}", style="dim"), "poor": Text("need more", style="red"),
                  "buy": Text("can buy", style="bold yellow"), "maxed": Text("full", style="dim")}[st]
        t.add_row(mark, Text(it["name"], style="bold" if st in ("equipped", "owned") else ""), Text(it["desc"], style="dim"),
                  Text(f"{it['price']:,}" if st not in ("owned", "equipped") else "—", style="gold1"), status)
    more = Text(f"{coin_state()['bal']:,} {ci()} to spend · press e to buy, equip or preview" + (f" · {above} above" if above else "")
                + (f" · {below} more below (↓)" if below else ""), style="dim")
    return Group(t, more)

# =============================================================================
# TUTORIAL / GUIDE (key b): a paged, scrollable explanation of every feature and of the game.
# Numbers (XP values, caps, level curve, streak rules) are read from the live game config, so the
# guide stays correct when you edit lookout_game.json. Opens automatically on the very first launch.
# Item kinds: ("h", heading) ("p", paragraph) ("i", bullet) ("k", key, description) ("s",) spacer
# =============================================================================
TUT = {"seen": False, "page": 0, "scroll": 0}
TUT_NAMES = ["Intro", "Screen", "Views", "Keys", "Tools", "Safety", "Game", "Quests", "More"]
SOUND_NAMES = "intro, notify, notify2, notify3, government, level_up, quest_complete, bounty_claimed, achievement, title_unlock, streak_milestone, shop_unlock, cache_open, boot, shutdown, mission_start, mission_complete, mission_failed, mission_tick"

def _tut_cfg(key, default):
    return GCFG.get(key, default) if GCFG else default

def tutorial_pages() -> list:
    rules = _tut_cfg("xp_rules", GAME_DEFAULT_XP)
    caps = _tut_cfg("xp_caps", GAME_DEFAULT_CAPS)
    st = _tut_cfg("settings", GAME_DEFAULT_SETTINGS)
    xs = GAME["level_xp"] if len(GAME["level_xp"]) > 1 else game_level_curve(st)
    ranks = _tut_cfg("ranks", [])
    off = [("p", "The game layer is currently OFF (started with --no-game), so none of this is active this run."), ("s",)] if not GAME["on"] else []

    intro = [
        ("h", "Welcome to Signal OPS"),
        ("p", "Signal OPS passively listens to Bluetooth Low Energy (BLE) advertisements: the small 'I'm here' broadcasts that phones, "
              "watches, earbuds, trackers, cars and smart-home gadgets send constantly. It never connects to or pairs with anything."),
        ("p", "It works out what each device probably is, estimates how close it is from its signal strength, flags anything "
              "security-relevant, and wraps it all in a game with XP, levels, quests and achievements."),
        ("s",), ("h", "Quick start"),
        ("i", "Leave the scan running (Scan: ON in the top bar) and walk around. New devices pop up and earn XP."),
        ("i", "Press v or the arrow keys to flip through views, or w to pick one from a list."),
        ("i", "Press p for your player profile, h for the full key list, and b any time to reopen this guide."),
        ("i", "Press q or Esc to quit. An HTML session report is saved automatically."),
        ("s",), ("h", "Good to know"),
        ("i", "Everything is passive and local. Distances are rough estimates from signal strength, not exact measurements."),
        ("i", "Many phones change their Bluetooth address about every 15 minutes. The scanner links those changes back to one "
              "device (a 'ghost') so you aren't counted as meeting a new stranger each time."),
        ("i", "ALERT and POSSIBLE flags are educated guesses from names, vendor IDs and services. Treat them as hints, not proof."),
        ("s",), ("p", "Use ← / → to change page, ↑ / ↓ (or j / k) to scroll, 1-9 to jump to a page, b to close."),
    ]
    screen = [
        ("h", "The top bar (HUD)"),
        ("k", "Row 1", "App name, your player name (it sparkles for supporters), then Scan / Dedup / Mute / Notify state, the signal "
                       "filter (Sig), AutoTac if enabled, and warnings for followers or an active hunt."),
        ("k", "Row 2", "Your level and XP bar, time scanned this session, devices seen, tactical devices in range, current view."),
        ("k", "Row 3", "Clock, battery, a heartbeat trace that beats faster as packets arrive, and the Bluetooth adapter in use."),
        ("k", "Row 4", "'Almost there': the quests and bounties closest to done, plus your daily streak."),
        ("k", "Mission row", "While a mission runs: its name, the countdown, and progress on each objective."),
        ("s",), ("h", "Reading a device line"),
        ("k", "● / ○", "LIVE (heard in the last 5 seconds) or recent / gone."),
        ("k", "✦ NEW", "A device that just appeared flashes for a couple of seconds."),
        ("k", "Name", "Your custom name if you gave one, otherwise its advertised name, otherwise what the scanner thinks it is."),
        ("k", "Ghost ×N", "The device has changed its private address N times; those addresses are linked as one device."),
        ("k", "Signal", "RSSI in dBm (closer to 0 is stronger), a 4-bar meter, an estimated distance in feet, and an arrow: "
                        "↑ getting closer, ↓ moving away, → steady."),
        ("s",), ("h", "Colours and tiers"),
        ("k", "Red ALERT", "A strong match for tactical gear such as body cameras, license-plate readers or drone controllers."),
        ("k", "Yellow", "POSSIBLE: weaker evidence of the same kind of device."),
        ("k", "Green", "A device from your known-devices file."),
        ("k", "Category", "Every other device is filed under a category (phones, wearables, trackers, smart home, ...)."),
    ]
    views = [
        ("p", "Press v (or →) for the next view and V (or ←) for the previous one. Press w to choose from a numbered list. "
              "Start in a specific view with --view NAME."),
        ("s",),
        ("k", "Standard Grid", "Every category as its own panel, plus a session summary. The default overview."),
        ("k", "Top 5", "The five busiest categories right now, as live panels."),
        ("k", "Compact List", "One dense table of every device in range, strongest first."),
        ("k", "Tactical", "ALERT / POSSIBLE devices and known-device matches only."),
        ("k", "Security Watch", "Tactical flags, follower alerts, watchlist devices, hacking tools and trackers on one screen."),
        ("k", "Proximity", "Every device ordered by closeness, with distance rings (10 / 30 / 100 ft)."),
        ("k", "Radar Sweep", "A rotating radar: distance comes from signal strength; the angle is arbitrary (BLE has no bearing)."),
        ("k", "New Arrivals", "Devices first heard in the last 5 minutes, newest first."),
        ("k", "Statistics", "Category mix, signal spread, address types, top vendors and session numbers."),
        ("k", "MAC Rotation", "Clusters of rotating addresses that look like the same physical device."),
        ("k", "Known & Named", "Devices you renamed, flagged or listed in your known-devices file."),
        ("k", "Per category", "One full-screen list for each category, including any you add in scanner_config.json."),
    ]
    keys = [
        ("h", "Scanning and sound"),
        ("k", "s", "Pause or resume scanning (paused time doesn't count)."),
        ("k", "m", "Mute or unmute all sounds."),
        ("k", "n / N", "Cycle the new-device sound: notify, notify2, notify3, off."),
        ("k", "z / o", "Toggle visual effects / CRT scanlines. Space skips a celebration card."),
        ("s",), ("h", "Filtering"),
        ("k", "d", "Dedup: collapse rotating addresses into one line."),
        ("k", "[ / ]", "Loosen / tighten the minimum signal (off, -90, -80, -70, -60, -50 dBm)."),
        ("k", "l", "Type an exact minimum signal in dBm."),
        ("k", "a", "Let alerts, known devices and the hunted device bypass the signal filter."),
        ("s",), ("h", "Devices"),
        ("k", "r", "Rename a device permanently."),
        ("k", "i", "Ignore a device by MAC or by name pattern. '-text' undoes one, 'list' shows them."),
        ("k", "c / Enter", "Inspect a device in detail. c closes the inspector."),
        ("k", "g / e", "Hunt a device. In the hunt view, e ends the hunt."),
        ("k", "f / x", "Follower Watch / mark a tracker as yours."),
        ("k", "u", "Toggle auto-switching to the Tactical view when a tactical device appears."),
        ("s",), ("h", "Views, game and misc"),
        ("k", "v / V / w", "Next view / previous view / pick a view. ← and → work too."),
        ("k", "p / t", "Player profile / equip a title or change your name."),
        ("k", "y", "Mission board: timed challenges. 1-9 starts one, 0 abandons the running one. (With the inspector open, y connects to that device instead.)"),
        ("k", "e", "Coin Exchange: spend Intel Coins on themes, neon mode and glitch effects."),
        ("k", "b", "This guide."),
        ("k", "h or ?", "Quick key reference."),
        ("k", "$", "Support the developer."),
        ("k", "q / Esc", "Quit."),
    ]
    tools = [
        ("h", "Rename (r)"),
        ("p", "Pick a device from the list or type its MAC and give it a name. Names are saved and survive restarts. "
              "If the device later rotates to a new address, the new one inherits your name."),
        ("s",), ("h", "Ignore (i)"),
        ("p", "Hide a device permanently by MAC, or hide every device whose name matches. Plain text is an exact name; "
              "wildcards work (Galaxy*, *TV*); re:<regex> is a regular expression. Put - in front to undo, or type list to see everything ignored."),
        ("s",), ("h", "Inspect (c or Enter)"),
        ("p", "A full-screen detail view: identity and why it was classified that way, vendor, services, signal and a 20-second history graph, "
              "first and last heard, linked addresses, and follower status."),
        ("s",), ("h", "Hunt (g)"),
        ("p", f"Pick a device and the scanner becomes a hot / cold locator: a signal meter, a trend arrow, a sonar display, and Geiger ticks (geiger_tick sound file, or a beep if it is missing) that speed up as "
              f"you get closer. The target counts as located at {HUNT_FOUND_RSSI} dBm or stronger, held for {HUNT_HOLD:.0f} seconds. Press e to end it. "
              "Devices with rotating addresses can slip away mid-hunt."),
        ("s",), ("h", "Signal filter ([ ] l a)"),
        ("p", "Hide weak, far-away devices so only things near you show up. A device only counts toward 'seen' (and your XP) once it clears the filter. "
              "The setting is saved."),
        ("s",), ("h", "Dedup and ghosts (d)"),
        ("p", "Private addresses rotate, so one phone can look like many. The scanner fingerprints the shape of each advertisement and "
              "links rotations that look like the same device. This is a probabilistic match, not a guarantee."),
        ("s",), ("h", "Known devices"),
        ("p", "lookout_known.json holds your renames, ignore rules, trusted trackers and a watchlist. scanner_config.json adds custom company IDs, "
              "OUIs, name terms and new categories (check it with --check-config)."),
    ]
    safety = [
        ("h", "Tactical flags"),
        ("p", "Devices that look like body cameras, license-plate readers, police or fleet radios, drones and similar are marked ALERT (strong evidence) "
              "or POSSIBLE (weaker). The Tactical and Security Watch views collect them, and each flagged device is logged in the session report."),
        ("s",), ("h", "Auto Tactical (u)"),
        ("p", "When on, the scanner jumps to the Tactical view and plays a sound the first time each new ALERT or POSSIBLE device appears. "
              "It won't interrupt a hunt or the inspector. The setting is saved, and AutoTac: ON shows in the top bar."),
        ("s",), ("h", "Follower Watch (f)"),
        ("p", "Looks for trackers (AirTag, Tile, SmartTag and similar) that keep staying close to you across different places. There is no GPS, "
              "so a 'place' is inferred from changes in the fixed devices around you."),
        ("k", "WATCH", f"Close to you for {fmt_dur(FOLLOW['watch_s'], True)}, movement unknown."),
        ("k", "SUSPECT", f"Seen across 2 places and close for {fmt_dur(FOLLOW['suspect_s'], True)}."),
        ("k", "ALERT", f"Seen across 3 places and close for {fmt_dur(FOLLOW['alert_s'], True)}. A banner and sound fire automatically."),
        ("p", "Press x to mark a tracker as yours so it stops alerting. --follow-all also watches ordinary fixed-address devices (noisier). "
              "Limits: a tracker that rotates its address is only followed while one address lasts, and with few fixed devices around, movement can't be seen."),
        ("p", "If an unknown tracker keeps following you, take it seriously: move to a public place and consider contacting local authorities."),
    ]
    game = off + [
        ("h", "The idea"),
        ("p", "Exploring the radio world around you earns XP. XP raises your level and rank; quests, bounties and achievements pay bonus XP. "
              "Progress is saved in lookout_profile.json."),
        ("s",), ("h", "How you earn XP"),
    ]
    for ev, desc in GAME_XP_EVENTS.items():
        amt, cap = rules.get(ev, 0), caps.get(ev)
        game.append(("k", f"+{amt} XP", desc[0].upper() + desc[1:] + (f"  (max {cap} XP/day)" if cap else "")))
    marks = [lv for lv in (2, 5, 10, 25, 50) if lv <= len(xs)]
    game += [
        ("s",), ("h", "Levels"),
        ("p", f"There are {len(xs)} levels. Total XP needed: " + ", ".join(f"level {lv} = {xs[lv - 1]:,}" for lv in marks) +
              ". Each level costs a bit more than the last."),
    ]
    if ranks:
        game.append(("p", "Ranks: " + ", ".join(f"{nm} (level {lv})" for lv, nm in ranks) + "."))
    game += [
        ("s",), ("h", "Good to know"),
        ("i", "A device only counts once per session, even if its address rotates."),
        ("i", "Daily caps (above) limit how much XP one activity can pay per day. You get a message when you reach one."),
        ("i", "Press p for your profile: overview, daily quests, bounties, achievements and titles (←/→ pages, ↑/↓ scroll)."),
        ("i", "Level-ups and unlocks trigger full-screen celebration cards with their own sounds. z turns the visuals off."),
    ]
    game += [
        ("s",), ("h", f"Intel Coins {ci()}"),
        ("p", "Playing also earns Intel Coins: quests, bounties, missions, achievements, level-ups, streak milestones, tactical finds, hunts, new categories, "
              "scan time and batches of new devices. Your balance sits next to your XP in the top bar; the Intel Coins page of your profile (p) lists every way to earn them."),
        ("p", "Press e to open the Coin Exchange and trade them for:"),
        ("i", "Interface themes (Matrix, Amber CRT, Cyber Ice, Phantom, Toxic Waste, Synthwave, Prism) that re-tint the whole scanner. Red ALERT text always stays red."),
        ("i", "Neon Mode: colours glow and breathe and panel borders become light tubes. It stacks with any theme."),
        ("i", "Glitch effects: random bursts of screen tearing, colour splitting and corruption. z turns every animation off."),
        ("i", "Decrypt Status Line: status messages scramble, then decode."),
        ("p", "In the exchange, a number buys that item (it is equipped straight away) or equips / removes something you own. pN previews item N for 10 seconds first. "
              "Prices, rewards, daily caps and level requirements are all in lookout_game.json (coin_rules, coin_caps, shop)."),
    ]
    reset_h = st.get("day_rollover_hour", 0)
    quests = off + [
        ("h", "Daily quests"),
        ("p", f"Each day you get {st.get('daily_quest_count', 3)} quests, such as seeing a number of devices or finding a certain category. "
              f"They reset at {reset_h:02d}:00 local time (the profile shows the countdown). Finishing one pays XP."),
        ("s",), ("h", "Bounties"),
        ("p", "Bounties are 'find this kind of device' targets, rated EASY, MEDIUM, HARD or ELITE. Some are one-time, others repeat daily. "
              "Some need several finds. Harder bounties pay far more XP."),
        ("s",), ("h", "Missions (y)"),
        ("p", "Missions are timed challenges, like 'find 5 different vendors in 3 minutes'. Press y (with the inspector closed), pick one by its number and the clock starts; "
              "the countdown sits in the top bar whatever view you are on. Only devices you hear for the first time after the start count, so walk around. "
              "The clock only runs while scanning is on."),
        ("p", "Finish in time for XP and Intel Coins, plus a speed bonus if at least half the clock is left. Run out of time and you lose nothing. "
              "Most missions pay once a day (you can still replay them for fun), and a daily coin cap stops farming. 0 on the board abandons a mission (press it twice). "
              "Missions count toward daily quests, achievements and titles through the missions_completed metric."),
        ("s",), ("h", "Achievements"),
        ("p", "Lifetime milestones: devices seen, scan time, hunts won and more. Hidden ones show as ??? until you earn them."),
        ("s",), ("h", "Titles"),
        ("p", "Unlock titles by reaching levels or earning achievements, bounties or quests. Press t to equip one (it shows in your HUD and profile) "
              "or to change your player name."),
        ("s",), ("h", "Daily streak"),
        ("p", f"Scan at least {st.get('streak_min_scan_minutes', 5):g} minutes in a day to count it toward your streak. Each extra streak day adds "
              f"{st.get('streak_bonus_xp', 10)} XP per day of streak (up to {st.get('streak_bonus_cap', 7)} days' worth), and milestones "
              "(3 days, every 7 days, 30, 60, 100 and so on) pay a big bonus. Miss a day and it resets, unless a Streak Shield covers it."),
        ("s",), ("h", "Daily surge, caches, weekly ops and shields"),
        ("p", f"Daily Surge: your first {ret_cfg()['surge']['minutes']:g} minutes of scanning each day pay x{ret_cfg()['surge']['multiplier']:g} XP on everything you discover (devices, vendors, categories, flags, scan time). "
              "The clock only runs while you scan and shows in the HUD, so even a short session earns well."),
        ("p", "Daily Caches: finishing some of today's quests opens loot boxes (bronze, silver, gold) with XP, coins and sometimes a Streak Shield or a jackpot. "
              "The quests page shows how close the next cache is."),
        ("p", f"Weekly Ops: {ret_cfg()['weekly_count']} bigger goals that reset every Monday (see the Weekly ops page of the profile). Finish them all to open the Weekly Chest."),
        ("p", f"Streak Shields: each covers one missed day automatically (hold up to {shield_max()}). Earn one every {ret_cfg()['shield']['free_every']} streak days, "
              "from caches, or buy them in the Coin Exchange. The streak ladder also pays coins on every streak day. Come back after "
              f"{ret_cfg()['comeback']['min_days_away']}+ days away and you get a Welcome Back bonus."),
        ("s",), ("h", "Customising the game"),
        ("p", "All quests, bounties, achievements, titles, ranks, XP values and the level curve live in lookout_game.json. You can edit it while the "
              "scanner runs and it reloads on its own. python3 scanner.py --check-game validates it and lists every metric you can use."),
    ]
    more = [
        ("h", "Effects and sound"),
        ("p", "z toggles visual effects: new-device flash, alert pulse, radar sweep, hunt sonar, heartbeat, XP shimmer and celebration cards. "
              "o toggles the CRT scanlines. m mutes everything."),
        ("p", "Sounds are plain files next to the script (.wav, .mp3, .ogg or .flac): " + SOUND_NAMES +
              ". A missing file falls back to notify, then the terminal bell. intro plays at launch and other sounds wait for it. geiger_tick is the hunt-mode Geiger click (random timing, faster and louder when closer)."),
        ("p", "On launch a short boot sequence plays (adapter handshake, database loading, ACCESS GRANTED) and starts the intro sound (an optional boot.mp3 plays the moment the sequence starts). Any key skips it, "
              "--no-boot skips it for one run, and the 'boot' block of lookout_game.json turns it off or tunes it."),
        ("p", "When you quit, a SESSION COMPLETE screen recaps the session: time online, devices seen, packets, XP earned, level, streak, Intel Coins, "
              "quests / bounties / missions done and the milestones you hit, with the shutdown sound. A key press finishes the reveal, the next closes it."),
        ("s",), ("h", "Files it creates"),
        ("k", "settings", "lookout_settings.json: signal filter, effects, notify sound, auto-tactical, supporter."),
        ("k", "profile", "lookout_profile.json: your level, XP, quests, achievements and streak."),
        ("k", "known", "lookout_known.json: renames, ignores, trusted trackers, watchlist."),
        ("k", "report", "session_logs/*.html: a full session report written when you quit."),
        ("s",), ("h", "Useful command-line options"),
        ("k", "--view NAME", "Start in a view (grid, radar, security, cat:<category>, ...)."),
        ("k", "--min-rssi", "Start with a minimum signal, e.g. -80."),
        ("k", "--adapter", "Pick the Bluetooth adapter (Linux), e.g. hci0."),
        ("k", "--no-fx", "Turn off animations for this run."),
        ("k", "--no-boot", "Skip the startup sequence for this run."),
        ("k", "--no-outro", "Skip the SESSION COMPLETE recap when you quit (--test-outro previews it)."),
        ("k", "--no-game", "Turn off XP, quests and the profile."),
        ("k", "--no-report", "Skip the end-of-session report."),
        ("k", "--tutorial", "Open this guide at startup."),
        ("k", "--update-db", "Download the IEEE and Bluetooth SIG databases for better identification."),
        ("s",), ("h", "Supporting the project"),
        ("p", "Press $ to see how to donate. Supporters get a sparkling name in the HUD and a gold SUPPORTER badge on their profile. "
              "It runs on the honor system, and every safety feature stays free for everyone."),
    ]
    return [intro, screen, views, keys, tools, safety, game, quests, more]

def tutorial_lines(items, width: int) -> list:
    """Items -> one Text per screen line, pre-wrapped so scrolling is exact."""
    kw = min(18, max([len(it[1]) for it in items if it[0] == "k"] or [8]))
    out = []
    for it in items:
        kind = it[0]
        if kind == "s":
            out.append(Text(""))
        elif kind == "h":
            out.append(Text(it[1], style="bold yellow"))
        elif kind == "p":
            out += [Text(ln) for ln in (textwrap.wrap(it[1], width) or [""])]
        elif kind == "i":
            out += [Text(ln) for ln in textwrap.wrap(it[1], width, initial_indent="  • ", subsequent_indent="    ")]
        elif kind == "k":
            body = textwrap.wrap(it[2], max(12, width - kw - 3)) or [""]
            for n, ln in enumerate(body):
                t = Text(no_wrap=True, overflow="crop")
                t.append("  " + (it[1].ljust(kw) if n == 0 else " " * kw), style="bold cyan")
                t.append(" " + ln)
                out.append(t)
    return out

def build_tutorial_panel(size):
    W, H = size
    pages = tutorial_pages()
    n = len(pages)
    TUT["page"] %= n
    page = TUT["page"]
    lines = tutorial_lines(pages[page], max(30, W - 8))
    fit = max(3, H - 6)
    TUT["scroll"] = max(0, min(TUT["scroll"], max(0, len(lines) - fit)))
    s = TUT["scroll"]
    vis = lines[s:s + fit]
    tabs = Text(no_wrap=True, overflow="ellipsis")
    if W >= 95:
        for i, nm in enumerate(TUT_NAMES):
            tabs.append(f" {i + 1} {nm} ", style="reverse bold" if i == page else "dim")
            tabs.append(" ")
    else:
        tabs.append(f" {page + 1}/{n} {TUT_NAMES[page]} ", style="reverse bold")
    above, below = s, max(0, len(lines) - s - len(vis))
    foot = Text(no_wrap=True, overflow="ellipsis", style="dim")
    foot.append(f"page {page + 1}/{n}")
    if above:
        foot.append(f" · {above} line(s) above (↑)")
    if below:
        foot.append(f" · {below} more below (↓)")
    return Panel(Group(tabs, Text(""), *vis, foot), title="[bold]📖 Guide[/]", title_align="left",
                 subtitle="←/→ page · ↑/↓ or j/k scroll · 1-9 jump · b close · h keys", border_style="bright_cyan", box=ROUNDED)

def tutorial_key():
    if CFG["show_tutorial"]:
        toggle_overlay("tutorial")
    else:
        open_overlay("tutorial")
        TUT.update(page=0, scroll=0)

def tutorial_nav(ch: str):
    n = len(TUT_NAMES)
    if ch in ("RIGHT", "LEFT"):
        TUT["page"] = (TUT["page"] + (1 if ch == "RIGHT" else -1)) % n
        TUT["scroll"] = 0
    elif ch in ("DOWN", "j"):
        TUT["scroll"] += 1
    elif ch in ("UP", "k"):
        TUT["scroll"] = max(0, TUT["scroll"] - 1)
    elif len(ch) == 1 and ch.isdigit() and 1 <= int(ch) <= n:
        TUT["page"], TUT["scroll"] = int(ch) - 1, 0

def donate_flow() -> str:
    """Support the developer: explain, ask for agreement, show the PayPal link and the unlock code, then activate (honor system)."""
    console = Console()
    sys.stdout.write("\033[H\033[J")
    if SUPPORT["on"]:
        console.print(Panel(Group(sparkle_text("SUPPORTER", time.time()), Text(""),
                                  Text("Your supporter status is already active. Thank you for supporting the project!"),
                                  Text(""), Text("Want to give again? " + DONATE_URL, style="dim")),
                            title="[bold yellow]Thank you[/]", border_style="yellow", box=ROUNDED))
        ask("\nPress Enter to return. ")
        return "Supporter status is already active. Thank you!"
    body = Group(
        Text("This scanner is built and maintained by one developer.", style="bold"),
        Text("If you find it useful, you can support it with a donation of any amount via PayPal.", style=""),
        Text(""),
        Text("Supporters unlock:", style="bold yellow"),
        Text("  ✦ a sparkling player name in the HUD"),
        Text("  ✦ a gold, sparkling SUPPORTER badge on your profile"),
        Text(""),
        Text("It runs on the honor system: nothing is checked or tracked, and every safety feature stays free for everyone.", style="dim"),
    )
    console.print(Panel(body, title="[bold yellow]★ Support the developer[/]", border_style="yellow", box=ROUNDED))
    agree = ask("\nDo you agree to make a donation to unlock supporter status? (yes / no): ").lower()
    if agree not in ("y", "yes"):
        return "No problem. Donate any time with $."
    print("\n1) Donate here (copy this link into your browser):\n")
    print(f"   {DONATE_URL}\n")
    print("2) After donating, your unlock code is:\n")
    print(f"   {SUPPORT_CODE}\n")
    entered = ask("3) Type the unlock code to activate supporter status (blank to cancel): ")
    if not entered:
        return "Cancelled. Press $ again when you're ready to enter the code."
    if entered.strip().upper() != SUPPORT_CODE.upper():
        return "That code doesn't match. Press $ to try again."
    SUPPORT["on"] = True
    save_settings()
    game_fx("achievement", "★ SUPPORTER", "Thank you for supporting the developer!", "Sparkling name unlocked")
    if GAME["on"]:
        game_note("★ SUPPORTER status activated. Thank you!", "achievement", True)
    return "★ Supporter status activated. Thank you for your support!"

def title_flow() -> str:
    """Equip an unlocked title, clear it, or rename the player. Returns a status-line message."""
    if not GAME["on"]:
        return "Game layer is off (started with --no-game)."
    owned = [t for t in GCFG["titles"] if t["id"] in STATE["titles"]]
    console = Console()
    sys.stdout.write("\033[H\033[J")
    table = Table(title=Text(f"Titles for {STATE['name']}"), box=ROUNDED)   # Text, not a str: names must never be parsed as markup
    table.add_column("#", justify="right", style="bold yellow")
    table.add_column("", width=1)
    table.add_column("Title")
    table.add_column("Unlocked by", style="dim")
    for n, t in enumerate(owned, 1):
        table.add_row(str(n), "★" if STATE["title"] == t["id"] else "", Text(t["name"]), Text(_req_text(t)))
    if not owned:
        console.print("[dim]No titles unlocked yet.[/]")
    else:
        console.print(table)
    choice = ask("Number to equip, '-' for no title, 'n' to change your player name (blank = cancel): ")
    if not choice:
        return "Cancelled."
    if choice.lower() == "n":
        new = clean(ask(f"Player name (now '{STATE['name']}'): "), 24)
        if not new:
            return "Name unchanged."
        STATE["name"] = new
        GAME["dirty"] = True
        game_save()
        return f"Player name set to {new}"
    if choice == "-":
        STATE["title"] = ""
        GAME["dirty"] = True
        return "Title cleared."
    idx = parse_index(choice, len(owned))
    if not idx:
        return "Nothing changed."
    STATE["title"] = owned[idx - 1]["id"]
    GAME["dirty"] = True
    game_save()
    return f"Equipped title: {owned[idx - 1]['name']}"

def game_report_section() -> str:
    """HTML block for the end-of-session report (empty when the game is off)."""
    if not GAME["on"]:
        return ""
    lvl, into, need = game_progress()
    cards = _cards([("XP earned this session", f"+{GAME['session_xp']:,}"),
                    ("Level", f"{GAME['session_start_level']} → {lvl}" if lvl != GAME["session_start_level"] else str(lvl)),
                    ("Rank", game_rank(lvl) or "—"), ("Title", game_title_name() or "—"),
                    ("Intel Coins", f"+{GAME['session_coins']:,} (balance {coin_state()['bal']:,})"),
                    ("Streak", f"{STATE['streak']} day(s)"), ("Total XP", f"{STATE['xp']:,}"),
                    ("Missions today", f"{int(game_day()['c'].get('missions_completed', 0))} completed")])
    if GAME["session_log"]:
        items = "".join(f'<li><span class="muted">{_e(_ts(t))}</span>{_tag("game", k.upper())}<span>{_e(x)}</span></li>'
                        for t, k, x in GAME["session_log"])
        log = f'<ul class="tl" style="margin-top:12px">{items}</ul>'
    else:
        log = '<p class="muted" style="margin-top:12px">No unlocks this session.</p>'
    return _section("Progress this session", cards + log)

def main():
    p = argparse.ArgumentParser(description="Signal OPS IRL v5 Tool")
    p.add_argument("--update-db", action="store_true", help="download IEEE OUI + Bluetooth SIG databases, then exit")
    p.add_argument("--known", default=KNOWN_FILE, help="known-devices file")
    p.add_argument("--follow-all", action="store_true",
                   help="follower detection also watches ordinary fixed-address devices, not just trackers (noisier)")
    p.add_argument("--config", default=CONFIG_FILE, help="device / OUI / category config (default: scanner_config.json)")
    p.add_argument("--min-rssi", type=int, default=None, metavar="DBM",
                   help="hide devices whose smoothed signal is weaker than this, e.g. -80 (0 = off). Overrides the saved setting")
    p.add_argument("--ignore-name", action="append", default=[], metavar="PATTERN",
                   help="hide devices whose advertised name matches (exact, wildcards like 'Galaxy*', or re:<regex>); repeatable, this run only. "
                        "For permanent rules use key i or \"ignore_names\" in the config")
    p.add_argument("--no-rssi-bypass", action="store_true",
                   help="apply the signal filter to alerts, known devices and the hunted device too")
    p.add_argument("--no-boot", action="store_true", help="skip the boot sequence (adapter handshake, loading bar, ACCESS GRANTED banner) for this run")
    p.add_argument("--boot", action="store_true", help="play the boot sequence even if lookout_settings.json turns it off")
    p.add_argument("--no-boot-sound", action="store_true", help="boot sequence without the intro sound")
    p.add_argument("--no-outro", action="store_true", help="skip the SESSION COMPLETE recap screen when you quit")
    p.add_argument("--test-outro", action="store_true", help="preview the SESSION COMPLETE recap screen with the current profile, then exit")
    p.add_argument("--classic", action="store_true", help="also discover classic Bluetooth (BR/EDR) devices (Linux/BlueZ; key k toggles it while running)")
    p.add_argument("--adapter", default="hci1", metavar="HCIn",
                   help="Bluetooth adapter to scan with (Linux/BlueZ), e.g. hci0. Default: hci1")
    p.add_argument("--view", default="proximity", metavar="NAME",
                   help="view to open at startup: grid, top5, compact, tactical, security, proximity, radar, arrivals, stats, ghosts, known, "
                        "or cat:<category> (default: proximity)")
    p.add_argument("--report-dir", default=REPORT_DIR, metavar="DIR", help="folder for the end-of-session HTML report (default: session_logs)")
    p.add_argument("--no-report", action="store_true", help="don't write the end-of-session HTML report")
    p.add_argument("--tutorial", action="store_true", help="open the guide / tutorial at startup (it also opens by itself on the very first launch)")
    p.add_argument("--no-fx", action="store_true", help="turn off the celebration effects and all live animations (flash, pulse, radar sweep, sonar, heartbeat, XP shimmer) for this run; sounds still play")
    p.add_argument("--test-fx", action="store_true", help="preview every celebration effect and its sound at startup")
    gp = p.add_argument_group("progression")
    gp.add_argument("--no-game", action="store_true", help="turn off XP, quests, bounties, achievements and the profile")
    gp.add_argument("--game-config", default=GAME_CONFIG_FILE, metavar="FILE", help="quests / bounties / achievements / titles config (default: lookout_game.json)")
    gp.add_argument("--profile", default=PROFILE_FILE, metavar="FILE", help="where player progress is saved (default: lookout_profile.json)")
    gp.add_argument("--player", metavar="NAME", help="set your player name")
    gp.add_argument("--check-game", action="store_true", help="validate the game config, list usable metrics, then exit")
    p.add_argument("--check-config", action="store_true", help="validate the config (categories, regexes, colours), print a summary, then exit")
    args = p.parse_args()

    if args.update_db:
        return update_db()
    if args.check_game:
        sys.exit(check_game_config(args.game_config))
    if args.check_config:
        print(f"[+] Config: {load_config(args.config)}")
        print("[+] Dashboard categories: " + ", ".join(c[0] for c in CATEGORIES))
        print("[+] Ignored names: " + (", ".join(CFG_IGNORE_NAMES) or "none"))
        print("[+] Tactical categories: " + (", ".join(f"{k} ({v})" for k, v in CFG_TACTICAL.items()) or "none"))
        for w in CFG_WARNINGS:
            print(f"[!] {w}")
        return
    if bleak is None or not HAVE_RICH:
        sys.exit("Missing dependencies. Install with:  pip install bleak rich")
    if not re.fullmatch(r"hci\d+", args.adapter):
        sys.exit("--adapter must look like hci0, hci1, ...")
    ADAPTER["name"] = args.adapter
    ADAPTER.update(adapter_details(args.adapter))
    _battery_refresh()                                # first reading up front so the HUD never flashes empty

    global KNOWN
    FOLLOW["scope"] = "all" if args.follow_all else "trackers"
    cfg_status = load_config(args.config)
    REG.load_all()
    load_settings()
    if args.min_rssi is not None:
        if args.min_rssi != 0 and not (-110 <= args.min_rssi <= -20):
            sys.exit("--min-rssi must be 0 (off) or between -110 and -20 dBm")
        CFG["min_rssi"] = None if args.min_rssi == 0 else args.min_rssi
    if args.no_rssi_bypass:
        CFG["rssi_bypass"] = False
    for pat in args.ignore_name:
        pat = pat.strip()
        if pat[:3].lower() == "re:":
            try:
                re.compile(pat[3:])
            except re.error as e:
                sys.exit(f"--ignore-name: invalid regular expression {pat!r}: {e}")
        if pat:
            SESSION_IGNORE_NAMES.append(pat)
    save_settings()
    if args.classic:
        CFG["classic"] = True
    if args.boot:
        CFG["boot"] = True
    if args.no_boot:
        CFG["boot"] = False
    if args.no_boot_sound:
        CFG["boot_sound"] = False
    if args.no_fx:
        CFG["fx"] = False
    print(f"[+] Config: {cfg_status}")
    for w in CFG_WARNINGS[:10]:
        print(f"[!] Config: {w}")
    KNOWN = KnownDevices(args.known)
    view_names = [v[0] for v in view_list()]          # after the config load, so config-defined categories exist
    if args.view in view_names:
        CFG["view_mode"] = view_names.index(args.view)
    else:
        print(f"[!] Unknown --view '{args.view}' (try: {', '.join(view_names[:10])}, cat:<category>); using the standard grid")
        CFG["view_mode"] = 0
    STATUS.set(f"Config: {cfg_status}")
    if not args.no_game:
        for w in game_init(args.game_config, args.profile, args.player)[:8]:
            print(f"[!] Game: {w}")
        game_session_start()
        print(f"[+] Player {STATE['name']}: level {game_level()}, {len(GCFG['quests'])} quests / {len(GCFG['bounties'])} bounties / "
              f"{len(GCFG['achievements'])} achievements / {len(GCFG['titles'])} titles")
    if args.test_fx:
        FX["hold_until"], FX["max_burst"] = 0.0, 99          # preview everything right away, uncollapsed
        game_fx("level", "New rank: Scout", "1,250 total XP", "", big2="7")
        game_fx("quest", "Signal Sweep", "See 25 new devices today", "+60 XP")
        game_fx("bounty", "Drone Hunter", "Elite bounty · Find a DJI drone", "+250 XP")
        game_fx("achievement", "🏆 Century Club", "See 100 devices in total", "+100 XP")
        game_fx("title", "Ghost Whisperer", "Link 10 MAC rotations", "Press t to equip")
        game_fx("streak", "🔥 7-DAY STREAK", "A full week of scanning", "+150 XP")
        game_fx("shop", "Matrix", "Interface theme", "-80 🪙 · equipped")
        game_fx("mission", "Vendor Rush", "1m 52s of 3m 00s · speed bonus", "+113 XP · +8 🪙")
        game_fx("mission_fail", "Vendor Rush", "3/5 different vendors", "Press y to try again")
    if args.test_outro:
        SESSION["start"] = SESSION["start"] or time.time() - 1800
        try:
            session_outro()
        except Exception as e:
            print(f"[!] Could not show the recap screen: {e}")
        return
    if args.tutorial or not TUT["seen"]:
        open_overlay("tutorial")
        STATUS.set("Welcome! This guide covers every feature and the game. ←/→ pages, b closes it, h lists the keys.")
        if not TUT["seen"]:
            TUT["seen"] = True
            save_settings()
    SESSION["start"] = time.time()
    log_event(f"Session started on {ADAPTER['name']}")
    BOOT["pending"], BOOT["cfg_status"] = boot_wanted(args.no_boot), cfg_status
    if not BOOT["pending"]:
        play_notification_sound("intro", intro=True)       # launch sound; all other sounds wait until it finishes (the boot sequence plays it itself)
    try:
        asyncio.run(amain(args))
    except KeyboardInterrupt:
        pass
    finally:
        game_save(force=True)                              # saved first, so nothing is lost if the recap screen is interrupted
        if outro_wanted(args.no_outro):
            try:
                session_outro()                            # plays the shutdown sound itself
            except BaseException:
                pass                                       # Ctrl+C or any display problem just skips the recap
        play_shutdown_sound()                              # no-op when the recap already played it
        print("[-] Scanner stopped.")
        if args.no_report:
            pass
        elif STATS["packets"] == 0 and SESSION["scan_seconds"] < 1:
            print("[-] No scan data recorded; session report skipped.")
        else:
            try:
                log_event("Session ended")
                print(f"[+] Session report saved: {write_session_report(args.report_dir)}")
            except Exception as e:
                print(f"[!] Could not write session report: {e}")

if __name__ == "__main__":
    main()
