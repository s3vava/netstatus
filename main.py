import ctypes
import ipaddress
import json
import logging
import os
import queue
import random
import socket
import ssl
import struct
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed, wait

import psutil
import requests

# GUI-библиотеки нужны только для виджета; режимы --net / --check работают и без них
try:
    import darkdetect
    import pystray
    from idlelib.tooltip import Hovertip
    from PIL import Image, ImageTk
    from pystray import MenuItem
    from tkinter import Tk, Label
    GUI_ERR = None
except Exception as _e:  # noqa
    GUI_ERR = _e

# =====================================================================
#  Конфиг
# =====================================================================
logging.basicConfig(
    filename=os.path.join(os.path.expanduser("~"), "myip_widget.log"),
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
)

DEFAULT_CONFIG = {
    "home_country_code": "RU",
    "proxy_url": "",
    "check_method": "tls",          # tls = рукопожатие (честная проверка), tcp = только connect
    "check_timeout": 2.0,
    "recheck_min": 5.0,             # один и тот же сервис не чаще, чем раз в 5-7 с
    "recheck_max": 7.0,
    "west_fail_streak": 3,          # сколько West-проверок подряд до подозрения на WL
    "west_slow_factor": 3,          # во сколько раз реже West при подтверждённом WL
    "burst_size": 5,
    "burst_timeout": 2.0,
    "burst_fast_interval": 0.3,
    "ru_interval_min": 5.0,
    "ru_interval_max": 7.0,
    "confirm_bursts": 2,
    "whitelist_threshold": 0.6,
    "ru_other_max_ok": 1,
    "local_poll_interval": 1.0,
    "ip_refresh_interval": 60,
    "request_timeout": 6,
    "count_system_proxy_as_vpn": True,
    "route_probe_ip": "1.1.1.1",
    "fake_ip_ranges": ["198.18.0.0/15"],
    "tunnel_min_prefix": 30,
    "vpn_adapter_keywords": ["tun", "tap", "wintun", "wireguard", "wg", "openvpn", "vpn",
                             "ppp", "happ", "sing-box", "singbox", "sing-tun", "xray",
                             "v2ray", "clash", "mihomo", "nekoray", "hiddify", "amnezia"],
    "vpn_adapter_ignore": ["teredo", "isatap", "6to4", "ip-https", "tunneling"],
    "virtual_adapter_keywords": ["vethernet", "virtualbox", "vmware", "loopback",
                                 "bluetooth", "hyper-v", "wsl", "docker", "npcap", "pseudo", "*"],
    "use_ping": True,
    "tcp_targets": [["77.88.8.8", 53], ["77.88.8.1", 53], ["77.88.8.8", 443]],
    "ping_targets": ["77.88.8.8", "77.88.8.1"],
    "groups": {
        "WEST": ["www.google.com", "www.cloudflare.com", "github.com",
                 "www.microsoft.com", "www.apple.com", "www.wikipedia.org"],
        "WL": ["ya.ru", "vk.com", "mail.ru", "www.gosuslugi.ru", "www.ozon.ru"],
        "RU_OTHER": ["habr.com", "pikabu.ru", "www.drive2.ru", "www.sports.ru",
                     "dtf.ru"],
    },
}


def app_dir():
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


def load_config():
    cfg = dict(DEFAULT_CONFIG)
    path = os.path.join(app_dir(), "config.json")
    try:
        with open(path, encoding="utf-8") as f:
            cfg.update(json.load(f))
        logging.info("config loaded: %s", path)
    except FileNotFoundError:
        logging.warning("config.json not found (%s), using defaults", path)
    except Exception as e:
        logging.error("config.json error: %s, using defaults", e)
    return cfg


CFG = load_config()


def resource_path(relative_path):
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, relative_path)


IMG_DIR = resource_path(os.path.join("assets", "images"))
PIRATE_FLAG = os.path.join(IMG_DIR, "pirate_flag.png")
ICON_FILE = os.path.join(IMG_DIR, "icon.ico")

COLOR_ON = "#33cc66"
COLOR_OFF = "#ff5555"
COLOR_WARN = "#ffaa33"
UA = "MyIPWidget/2.0"
NO_WINDOW = 0x08000000 if os.name == "nt" else 0


# =====================================================================
#  Локальное определение VPN (без запросов в интернет)
# =====================================================================
HW_PREFIXES = ("PCI\\", "USB\\", "ACPI\\", "PCMCIA\\", "SD\\")
_pnp_cache = (0.0, {})


def pnp_ids():
    """Windows: имя адаптера -> PnpInstanceID из реестра.
    PCI\\ и USB\\ = настоящее железо; ROOT\\, SWD\\ и т.п. = программный адаптер (TUN/TAP/Wintun)."""
    global _pnp_cache
    now = time.monotonic()
    if now - _pnp_cache[0] < 5:
        return _pnp_cache[1]
    out = {}
    try:
        import winreg
        base = r"SYSTEM\CurrentControlSet\Control\Network\{4D36E972-E325-11CE-BFC1-08002BE10318}"
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, base) as k:
            i = 0
            while True:
                try:
                    guid = winreg.EnumKey(k, i)
                except OSError:
                    break
                i += 1
                try:
                    with winreg.OpenKey(k, guid + r"\Connection") as c:
                        name = winreg.QueryValueEx(c, "Name")[0]
                        pnp = winreg.QueryValueEx(c, "PnpInstanceID")[0]
                        out[name] = pnp
                except OSError:
                    continue
    except Exception:
        pass
    _pnp_cache = (now, out)
    return out


def name_is_tunnel(name):
    n = name.lower()
    if any(x in n for x in CFG["vpn_adapter_ignore"]):
        return False
    return any(x in n for x in CFG["vpn_adapter_keywords"])


def prefix_len(mask):
    try:
        return bin(int(ipaddress.ip_address(mask))).count("1")
    except ValueError:
        return None


def in_fake_range(ip):
    try:
        a = ipaddress.ip_address(ip)
    except ValueError:
        return False
    return any(a in ipaddress.ip_network(n) for n in CFG["fake_ip_ranges"])


def list_adapters():
    """Туннельный адаптер определяется НЕ только по имени. Признаки (любой):
    имя из списка, адрес из диапазона fake-ip (198.18.0.0/15), маска /30 и уже
    (у LAN так не бывает), адаптер не аппаратный (нет PCI/USB в реестре)."""
    stats = psutil.net_if_stats()
    pnp = pnp_ids()
    out = []
    for name, addrs in psutil.net_if_addrs().items():
        v4 = [a for a in addrs if a.family == socket.AF_INET
              and not a.address.startswith(("127.", "169.254."))]
        ipv4 = [a.address for a in v4]
        prefix = prefix_len(v4[0].netmask) if v4 and v4[0].netmask else None
        st = stats.get(name)
        up = bool(st and st.isup)
        virt = any(k in name.lower() for k in CFG["virtual_adapter_keywords"])
        pnp_id = pnp.get(name)
        hardware = None if pnp_id is None else pnp_id.upper().startswith(HW_PREFIXES)

        why = []
        if up and ipv4 and not virt:
            if name_is_tunnel(name):
                why.append("имя")
            if any(in_fake_range(ip) for ip in ipv4):
                why.append("адрес в диапазоне fake-ip")
            if prefix is not None and prefix >= CFG["tunnel_min_prefix"]:
                why.append(f"маска /{prefix}")
            if hardware is False:
                kind = pnp_id.split("\\")[0]
                why.append(f"не аппаратный ({kind})")
        tun = bool(why)
        out.append({"name": name, "up": up, "ipv4": ipv4, "prefix": prefix,
                    "hardware": hardware, "tunnel": tun, "virtual": virt, "why": why,
                    "physical": up and bool(ipv4) and not tun and not virt})
    return out


def route_source_ip(dest):
    """Через какой локальный адрес система отправит пакет к dest.
    UDP connect ничего не отправляет, это только запрос к таблице маршрутов."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect((dest, 53))
        return s.getsockname()[0]
    except OSError:
        return None
    finally:
        s.close()


def system_proxy_on():
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                            r"Software\Microsoft\Windows\CurrentVersion\Internet Settings") as k:
            return bool(winreg.QueryValueEx(k, "ProxyEnable")[0])
    except Exception:
        return False


def local_state():
    adapters = list_adapters()
    src = route_source_ip(CFG["route_probe_ip"])
    src_adapter = next((a for a in adapters if src and src in a["ipv4"]), None)
    tunnel_default = bool(src_adapter and src_adapter["tunnel"])
    tunnels_up = [a["name"] for a in adapters if a["tunnel"] and a["up"] and a["ipv4"]]
    proxy = bool(CFG["count_system_proxy_as_vpn"]) and system_proxy_on()
    physical = [(a["name"], a["ipv4"][0]) for a in adapters if a["physical"]]

    reasons = []
    if tunnel_default:
        reasons.append(f"маршрут по умолчанию идёт через туннель "
                       f"({src_adapter['name']}: {', '.join(src_adapter['why'])})")
    if tunnels_up:
        reasons.append("активные туннельные адаптеры: " + ", ".join(tunnels_up))
    if proxy:
        reasons.append("включён системный прокси")

    return {
        "vpn": bool(reasons),
        "link": bool(physical),
        "src": src,
        "src_adapter": src_adapter["name"] if src_adapter else None,
        "tunnels": tunnels_up,
        "proxy": proxy,
        "physical": physical,
        "adapters": adapters,
        "reasons": reasons,
    }


# =====================================================================
#  Проверки доступности (TLS / TCP / ping)
# =====================================================================
TLS_CTX = ssl.create_default_context()
TLS_CTX.check_hostname = False
TLS_CTX.verify_mode = ssl.CERT_NONE   # важна достижимость, а не цепочка сертификатов

_dns_cache = {}
_dns_lock = threading.Lock()


def clear_dns_cache():
    with _dns_lock:
        _dns_cache.clear()


def is_ip(h):
    try:
        ipaddress.ip_address(h)
        return True
    except ValueError:
        return False


def resolve(host, timeout):
    if is_ip(host):
        return host
    now = time.monotonic()
    with _dns_lock:
        c = _dns_cache.get(host)
    if c and now - c[1] < 60:
        return c[0]
    res = []

    def work():
        try:
            res.append(socket.getaddrinfo(host, None, socket.AF_INET)[0][4][0])
        except OSError:
            pass

    t = threading.Thread(target=work, daemon=True)
    t.start()
    t.join(timeout)
    if res:
        with _dns_lock:
            _dns_cache[host] = (res[0], now)
        return res[0]
    return c[0] if c else None


def if_index(name):
    try:
        return socket.if_nametoindex(name)
    except Exception:
        return None


def bind_iface(s, ip, idx):
    """Привязка сокета к конкретному адаптеру (в обход туннеля), по возможности."""
    if idx:
        try:
            s.setsockopt(socket.IPPROTO_IP, 31, struct.pack("!I", idx))  # IP_UNICAST_IF
        except OSError:
            pass
    if ip:
        s.bind((ip, 0))


def check_target(host, port, bind_ip=None, idx=None, method=None, timeout=None):
    """True, если сервис ответил. Для tls проверяется реальный ответ сервера:
    это отсекает «фейковый» успех, когда TUN сам принимает соединение."""
    method = method or CFG["check_method"]
    timeout = timeout or CFG["check_timeout"]
    ip = resolve(host, timeout)
    if not ip:
        return False
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        s.settimeout(timeout)
        bind_iface(s, bind_ip, idx)
        s.connect((ip, int(port)))
        if method == "tls":
            ss = TLS_CTX.wrap_socket(s, server_hostname=None if is_ip(host) else host)
            ss.close()
        return True
    except (OSError, ssl.SSLError, ValueError):
        return False
    finally:
        try:
            s.close()
        except Exception:
            pass


def ping(host, src=None, timeout_ms=1000):
    if os.name == "nt":
        cmd = ["ping", "-n", "1", "-w", str(timeout_ms)] + (["-S", src] if src else []) + [host]
    else:
        cmd = ["ping", "-c", "1", "-W", "1", host]
    try:
        r = subprocess.run(cmd, capture_output=True, timeout=timeout_ms / 1000 + 2,
                           creationflags=NO_WINDOW)
        return b"TTL=" in r.stdout.upper()   # ответ шлюза «недоступен» без TTL не засчитывается
    except Exception:
        return False


def physical_probe(physical):
    """Есть ли РЕАЛЬНЫЙ интернет по физическому адаптеру (мимо туннеля):
    TCP и ping до Яндекс DNS с привязкой к адаптеру. True/False."""
    jobs = []
    for name, ip in physical:
        idx = if_index(name)
        for host, port in CFG["tcp_targets"]:
            jobs.append(lambda h=host, p=port, ip=ip, idx=idx:
                        check_target(h, p, ip, idx, "tcp", 1.5))
        if CFG["use_ping"]:
            for h in CFG["ping_targets"]:
                jobs.append(lambda h=h, ip=ip: ping(h, ip))
    if not jobs:
        return False
    ex = ThreadPoolExecutor(max_workers=len(jobs))
    try:
        futs = [ex.submit(j) for j in jobs]
        for f in as_completed(futs, timeout=4):
            try:
                if f.result():
                    return True
            except Exception:
                pass
    except Exception:
        pass
    finally:
        ex.shutdown(wait=False)
    return False


# =====================================================================
#  Определение внешнего IP (для отображения, не для статуса VPN)
# =====================================================================
def _ip_api(s):
    r = s.get("http://ip-api.com/json/?fields=status,message,country,countryCode,query",
              timeout=CFG["request_timeout"])
    r.raise_for_status()
    d = r.json()
    if d.get("status") != "success":
        raise ValueError(d.get("message", "ip-api: fail"))
    return d["query"], d["country"], d["countryCode"]


def _ipwho(s):
    r = s.get("https://ipwho.is/", timeout=CFG["request_timeout"])
    r.raise_for_status()
    d = r.json()
    if not d.get("success"):
        raise ValueError(d.get("message", "ipwho: fail"))
    return d["ip"], d["country"], d["country_code"]


def _ipapi_co(s):
    r = s.get("https://ipapi.co/json/", timeout=CFG["request_timeout"])
    r.raise_for_status()
    d = r.json()
    if "ip" not in d or "error" in d:
        raise ValueError(d.get("reason", "ipapi.co: fail"))
    return d["ip"], d["country_name"], d["country_code"]


def _2ip(s):
    r = s.get("https://api.2ip.ru/geo.json", timeout=CFG["request_timeout"])
    r.raise_for_status()
    d = r.json()
    ip, code = d.get("ip"), d.get("country_code")
    if not ip or not code:
        raise ValueError("2ip: unexpected response")
    return ip, d.get("country_rus") or d.get("country") or code, code


PROVIDERS = [_ip_api, _ipwho, _ipapi_co, _2ip]


def lookup_ip():
    """Каждый вызов создаёт НОВЫЕ соединения (Connection: close). Раньше сессия жила вечно,
    и keep-alive соединение продолжало идти старым путём после включения/выключения VPN."""
    for route in ("main", "direct"):
        s = requests.Session()
        s.headers.update({"User-Agent": UA, "Connection": "close"})
        if route == "direct":
            s.trust_env = False
        elif CFG.get("proxy_url"):
            s.trust_env = False
            s.proxies = {"http": CFG["proxy_url"], "https": CFG["proxy_url"]}
        ex = ThreadPoolExecutor(max_workers=len(PROVIDERS))
        futs = [ex.submit(p, s) for p in PROVIDERS]
        ex.shutdown(wait=False)
        try:
            for p, f in zip(PROVIDERS, futs):
                try:
                    res = f.result()
                    logging.info("IP via %s route=%s: %s %s", p.__name__, route, res[0], res[2])
                    return res
                except Exception as e:
                    logging.warning("%s route=%s failed: %s", p.__name__, route, e)
        finally:
            s.close()
    return None


def is_home(code):
    home = (CFG.get("home_country_code") or "").upper()
    return bool(home) and (code or "").upper() == home


# =====================================================================
#  Монитор: вся логика статусов
# =====================================================================
def parse_target(entry):
    e = entry.strip()
    for p in ("https://", "http://"):
        if e.startswith(p):
            e = e[len(p):]
    e = e.split("/")[0]
    if ":" in e:
        h, p = e.rsplit(":", 1)
        return h, int(p)
    return e, 443


class Target:
    def __init__(self, entry):
        self.host, self.port = parse_target(entry)
        self.next_due = 0.0
        self.busy = False


BAD_STATES = ("suspect", "whitelist", "foreign_blocked", "limited", "no_internet")


class Monitor(threading.Thread):
    """Состояния сети (self.state):
    checking        - после смены сети, ждём первых результатов West
    normal          - West отвечает
    suspect         - 3 West подряд не ответили, идёт быстрая проверка РФ (статус не определён)
    whitelist       - WL доступны, остальные РФ и West нет
    foreign_blocked - РФ доступны (в т.ч. вне WL), West нет
    limited         - сеть есть, но почти ничего не отвечает
    no_internet     - физически интернета нет (проверено мимо туннеля)
    """

    def __init__(self, out_q):
        super().__init__(daemon=True)
        self.out = out_q
        self.stop_event = threading.Event()
        self.pool = ThreadPoolExecutor(max_workers=24)
        self.bpool = ThreadPoolExecutor(max_workers=2)
        g = CFG["groups"]
        self.west = [Target(e) for e in g.get("WEST", [])]
        self.wl = [Target(e) for e in g.get("WL", [])]
        self.ru = [Target(e) for e in g.get("RU_OTHER", [])]
        random.shuffle(self.west)
        for i, t in enumerate(self.west):
            t.next_due = time.monotonic() + i * CFG["recheck_min"] / max(1, len(self.west))

        self.results = queue.Queue()
        self.local = None
        self.local_key = None
        self.epoch = 0
        self.state = "checking"
        self.west_streak = 0
        self.burst_future = None
        self.burst_epoch = 0
        self.burst_next = 0.0
        self.pending = (None, 0)
        self.ip_info = None
        self.ip_future = None
        self.ip_epoch = 0
        self.ip_next = 0.0
        self.ip_ok_at = 0.0
        self.ip_boost = []
        self.last_view = None

    # ---------- локальная сеть (каждую секунду) ----------
    def update_local(self, now):
        try:
            loc = local_state()
        except Exception:
            logging.exception("local_state failed")
            return
        key = (loc["vpn"], loc["link"], loc["src_adapter"],
               tuple(ip for _, ip in loc["physical"]))
        old = self.local_key
        self.local, self.local_key = loc, key
        if key != old:
            logging.info("local change: vpn=%s link=%s src=%s phys=%s reasons=%s",
                         loc["vpn"], loc["link"], loc["src_adapter"], loc["physical"],
                         loc["reasons"])
            self.on_change(now)

    def on_change(self, now):
        """Сеть изменилась: моментально сбрасываем состояние и запускаем проверки."""
        self.epoch += 1
        clear_dns_cache()
        self.west_streak = 0
        self.pending = (None, 0)
        self.state = "checking"
        self.ip_info = None
        self.ip_boost = [now + 0.5, now + 4.0]
        for i, t in enumerate(self.west):
            if not t.busy:
                t.next_due = now + i * 0.15
        self.burst_next = 0.0

    # ---------- West: постоянная ротация сервисов ----------
    def schedule_west(self, now):
        for t in sorted(self.west, key=lambda x: x.next_due):
            if not t.busy and t.next_due <= now:
                t.busy = True
                self.pool.submit(self._run_west, t, self.epoch)

    def _run_west(self, t, epoch):
        try:
            ok = check_target(t.host, t.port)
        except Exception:
            ok = False
        self.results.put((t, ok, time.monotonic(), epoch))

    def collect(self, now):
        while True:
            try:
                t, ok, ts, epoch = self.results.get_nowait()
            except queue.Empty:
                break
            t.busy = False
            mult = CFG["west_slow_factor"] if self.state == "whitelist" else 1
            t.next_due = ts + random.uniform(CFG["recheck_min"], CFG["recheck_max"]) * mult
            if epoch != self.epoch:
                continue
            logging.info("west %s -> %s", t.host, "ok" if ok else "FAIL")
            self.on_west(ok, now)

    def on_west(self, ok, now):
        if ok:
            self.west_streak = 0
            if self.state != "normal":
                logging.info("state %s -> normal", self.state)
                self.state = "normal"
                self.pending = (None, 0)
        else:
            self.west_streak += 1
            if self.west_streak >= CFG["west_fail_streak"] and self.state in ("normal", "checking"):
                logging.info("state %s -> suspect (west fails: %d)", self.state, self.west_streak)
                self.state = "suspect"
                self.pending = (None, 0)
                self.burst_next = now

    # ---------- РФ-проверки: только когда West недоступен ----------
    def tick_burst(self, now):
        if self.burst_future is not None:
            if not self.burst_future.done():
                return
            try:
                r = self.burst_future.result()
            except Exception:
                logging.exception("burst failed")
                r = None
            self.burst_future = None
            if r and self.burst_epoch == self.epoch and self.state in BAD_STATES:
                self.on_burst(r)
            if self.state == "suspect":
                self.burst_next = now + CFG["burst_fast_interval"]
            else:
                self.burst_next = now + random.uniform(CFG["ru_interval_min"],
                                                       CFG["ru_interval_max"])
            return
        if self.state in BAD_STATES and now >= self.burst_next:
            self.burst_epoch = self.epoch
            self.burst_future = self.bpool.submit(self._burst_job)

    def _burst_job(self):
        n = CFG["burst_size"]
        wl = random.sample(self.wl, min(n, len(self.wl)))
        ru = random.sample(self.ru, min(n, len(self.ru)))
        allt = wl + ru
        ex = ThreadPoolExecutor(max_workers=max(1, len(allt)))
        futs = {ex.submit(check_target, t.host, t.port, None, None, None,
                          CFG["burst_timeout"]): t for t in allt}
        wait(list(futs), timeout=CFG["burst_timeout"] + 2)
        ex.shutdown(wait=False)

        def ok(f):
            try:
                return f.done() and bool(f.result())
            except Exception:
                return False

        wl_ok = sum(1 for f, t in futs.items() if t in wl and ok(f))
        ru_ok = sum(1 for f, t in futs.items() if t in ru and ok(f))
        phys = True
        if wl_ok + ru_ok == 0:
            phys = physical_probe(self.local["physical"] if self.local else [])
        return {"wl": (wl_ok, len(wl)), "ru": (ru_ok, len(ru)), "phys": phys}

    def on_burst(self, r):
        wl_ok, wl_n = r["wl"]
        ru_ok, ru_n = r["ru"]
        wl_up = wl_n > 0 and wl_ok / wl_n >= CFG["whitelist_threshold"]
        if ru_ok > CFG["ru_other_max_ok"]:
            verdict = "foreign_blocked"
        elif wl_up:
            verdict = "whitelist"
        elif wl_ok + ru_ok > 0:
            verdict = "limited"
        else:
            verdict = "limited" if r["phys"] else "no_internet"
        logging.info("burst WL:%d/%d RU:%d/%d phys=%s -> %s (state=%s)",
                     wl_ok, wl_n, ru_ok, ru_n, r["phys"], verdict, self.state)
        if verdict == self.state:
            self.pending = (None, 0)
            return
        cnt = self.pending[1] + 1 if self.pending[0] == verdict else 1
        self.pending = (verdict, cnt)
        if cnt >= CFG["confirm_bursts"]:
            logging.info("state %s -> %s", self.state, verdict)
            self.state = verdict
            self.pending = (None, 0)

    # ---------- внешний IP (для отображения) ----------
    def tick_ip(self, now):
        if self.ip_future is not None and self.ip_future.done():
            try:
                res = self.ip_future.result()
            except Exception:
                res = None
            if self.ip_epoch == self.epoch:
                if res:
                    self.ip_info, self.ip_ok_at = res, now
            self.ip_future = None
        if self.ip_future is not None or self.state == "no_internet":
            return
        due = False
        if self.ip_boost and now >= self.ip_boost[0]:
            self.ip_boost.pop(0)
            due = True
        elif self.ip_info is None and now >= self.ip_next:
            due = True
        elif self.ip_info is not None and now - self.ip_ok_at >= CFG["ip_refresh_interval"]:
            due = True
        if due:
            self.ip_epoch = self.epoch
            self.ip_future = self.pool.submit(lookup_ip)
            self.ip_next = now + (3 if self.state in ("normal", "checking") else 15)

    # ---------- представление для виджета ----------
    def build_view(self):
        loc = self.local
        if not loc:
            return (None, "Loading...", "", "", None, "Loading")
        vpn = loc["vpn"]
        vtxt = "VPN ON" if vpn else "VPN OFF"
        vcol = COLOR_ON if vpn else COLOR_OFF
        st = self.state
        ip = self.ip_info
        if not loc["link"]:
            return (None, "No network", "", "NO LINK", COLOR_OFF, "No network link")
        if st == "no_internet":
            return (None, "No Internet", "", "OFFLINE", COLOR_OFF, "No Internet")
        if st == "limited":
            l2 = "VPN: no access" if vpn else "Limited access"
            return (None, l2, "", f"{vtxt} | NO RESPONSE", COLOR_WARN, l2)
        if st == "whitelist":
            return (None, "Whitelist mode", "", f"{vtxt} | WHITELIST", COLOR_WARN, "Whitelist mode")
        if st == "foreign_blocked":
            l2 = "VPN: no access" if vpn else "Foreign blocked"
            return (None, l2, "", f"{vtxt} | WEST BLOCKED", COLOR_WARN, l2)
        code, country, ipaddr = (ip[2], ip[1], ip[0]) if ip else (None, "Checking...", "")
        if st == "suspect":
            return (code, "Checking...", ipaddr, f"{vtxt} | WL?", COLOR_WARN, "Checking (WL?)")
        status = vtxt
        if vpn and ip and is_home(code):
            status += f" | {code} IP?"       # VPN включён, но сам виджет выходит в сеть напрямую
        return (code, country, ipaddr, status, vcol, f"{status} {ipaddr}".strip())

    def publish(self):
        v = self.build_view()
        if v != self.last_view:
            self.last_view = v
            self.out.put(("view", v))

    # ---------- главный цикл ----------
    def run(self):
        last_local = 0.0
        while not self.stop_event.is_set():
            now = time.monotonic()
            try:
                if now - last_local >= CFG["local_poll_interval"]:
                    last_local = now
                    self.update_local(now)
                self.collect(now)
                if self.local and self.local["link"]:
                    self.schedule_west(now)
                    self.tick_burst(now)
                    self.tick_ip(now)
                self.publish()
            except Exception:
                logging.exception("monitor loop error")
            self.stop_event.wait(0.2)


# =====================================================================
#  Виджет
# =====================================================================
class Application:
    def __init__(self):
        self.q = queue.Queue()
        self.last_view = None
        self._drag = (0, 0)
        self._flag_cache = {}

        self.root = Tk()
        self.root.overrideredirect(True)
        self.root.title("MyIP Widget")
        try:
            self.root.iconbitmap(ICON_FILE)
        except Exception as e:
            logging.warning("iconbitmap: %s", e)

        if darkdetect.theme() == "Dark":
            self.bg_color, self.fg_color = "black", "white"
        else:
            self.bg_color, self.fg_color = "white", "black"

        kw = dict(bd=0, bg=self.bg_color, fg=self.fg_color,
                  highlightthickness=0, borderwidth=0)
        self.lab1 = Label(self.root, bg=self.bg_color)
        self.lab2 = Label(self.root, **kw)
        self.lab3 = Label(self.root, **kw)
        self.lab4 = Label(self.root, font=("Segoe UI", 9, "bold"), **kw)
        for i, lab in enumerate((self.lab1, self.lab2, self.lab3, self.lab4), start=1):
            lab.grid(row=i, column=1)

        self.lab1.bind("<Button-3>", self.hide_window)
        Hovertip(self.lab1, "right click to close")

        self.root.attributes("-alpha", 0.7)
        self.root.attributes("-topmost", True)
        self.root.configure(bg=self.bg_color)
        self.root.bind("<ButtonPress-1>", self.start_move)
        self.root.bind("<B1-Motion>", self.move_window)

        self.show_flag(PIRATE_FLAG)
        self.lab2.config(text="Loading...")

        self.icon = pystray.Icon(
            "myip", Image.open(PIRATE_FLAG), "MyIP",
            menu=pystray.Menu(
                MenuItem("Show", lambda: self.q.put(("show", None))),
                MenuItem("Quit", lambda: self.q.put(("quit", None))),
            ),
        )
        self.icon.run_detached()

        self.monitor = Monitor(self.q)
        self.monitor.start()
        self.root.after(100, self.process_queue)

    def start_move(self, event):
        self._drag = (event.x_root - self.root.winfo_x(),
                      event.y_root - self.root.winfo_y())

    def move_window(self, event):
        self.root.geometry(f"+{event.x_root - self._drag[0]}+{event.y_root - self._drag[1]}")

    def hide_window(self, event=None):
        self.root.withdraw()

    def flag_path(self, code):
        if not code:
            return PIRATE_FLAG
        path = os.path.join(IMG_DIR, "flags", f"{code}.png")
        return path if os.path.exists(path) else PIRATE_FLAG

    def show_flag(self, path):
        if path not in self._flag_cache:
            pil = Image.open(path)
            pil.load()
            self._flag_cache[path] = (ImageTk.PhotoImage(pil), pil)
        photo, pil = self._flag_cache[path]
        self.lab1.config(image=photo)
        self.lab1.image = photo
        return pil

    def process_queue(self):
        try:
            while True:
                kind, data = self.q.get_nowait()
                if kind == "view":
                    self.render(data)
                elif kind == "show":
                    self.root.deiconify()
                elif kind == "quit":
                    self.shutdown()
                    return
        except queue.Empty:
            pass
        self.root.after(100, self.process_queue)

    def render(self, view):
        code, l2, l3, status, color, title = view
        pil = self.show_flag(self.flag_path(code))
        self.lab2.config(text=l2)
        self.lab3.config(text=l3)
        self.lab4.config(text=status, fg=color or self.fg_color)
        try:
            self.icon.icon = pil
            self.icon.title = title[:120]
        except Exception:
            pass

    def shutdown(self):
        self.monitor.stop_event.set()
        try:
            self.icon.stop()
        except Exception:
            pass
        self.root.destroy()

    def run(self):
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            try:
                ctypes.windll.user32.SetProcessDPIAware()
            except Exception:
                pass
        self.root.mainloop()
        os._exit(0)


# =====================================================================
#  Режимы отладки
# =====================================================================
def print_local(loc):
    print("Адаптеры:")
    for a in loc["adapters"]:
        tag = ("TUN " if a["tunnel"] else "PHYS" if a["physical"] else "virt" if a["virtual"]
               else "    ")
        hw = {True: "железо", False: "софт", None: "?"}[a["hardware"]]
        mask = f"/{a['prefix']}" if a["prefix"] is not None and a["ipv4"] else ""
        print(f"  [{tag}] {a['name']:<30} {'up  ' if a['up'] else 'down'}  "
              f"{', '.join(a['ipv4'])}{mask}  ({hw})"
              + (f"  <- {', '.join(a['why'])}" if a["why"] else ""))
    print(f"\nМаршрут к {CFG['route_probe_ip']}: источник {loc['src']} "
          f"(адаптер: {loc['src_adapter']})")
    print("Системный прокси:", "ВКЛ" if loc["proxy"] else "выкл")
    print("Физическая сеть (link):", "есть" if loc["link"] else "НЕТ")
    print("\n=> VPN:", "ON" if loc["vpn"] else "OFF")
    for r in loc["reasons"]:
        print("   -", r)


def cli_net(watch):
    loc = local_state()
    print_local(loc)
    if not watch:
        print("\nСовет: python main.py --net --watch  - покажет изменения в реальном времени")
        return
    print("\n--- слежение (Ctrl+C для выхода) ---")
    last = None
    try:
        while True:
            loc = local_state()
            cur = (loc["vpn"], loc["link"], loc["src_adapter"], tuple(loc["tunnels"]), loc["proxy"])
            if cur != last:
                print(time.strftime("%H:%M:%S"), "VPN", "ON " if loc["vpn"] else "OFF",
                      "| link:", loc["link"], "| route via:", loc["src_adapter"],
                      "| tunnels:", loc["tunnels"], "| proxy:", loc["proxy"])
                last = cur
            time.sleep(1)
    except KeyboardInterrupt:
        pass


def cli_check():
    logging.getLogger().addHandler(logging.StreamHandler(sys.stdout))
    loc = local_state()
    print("=== Локальный статус ===")
    print("VPN:", "ON" if loc["vpn"] else "OFF", "|", "; ".join(loc["reasons"]) or "нет признаков")
    print("Физический линк:", "есть" if loc["link"] else "НЕТ",
          [f"{n} {ip}" for n, ip in loc["physical"]])

    print("\n=== Внешний IP (только для отображения) ===")
    print(lookup_ip())

    def timed(t):
        t0 = time.monotonic()
        ok = check_target(t.host, t.port)
        return ok, int((time.monotonic() - t0) * 1000)

    for grp, entries in CFG["groups"].items():
        targets = [Target(e) for e in entries]
        with ThreadPoolExecutor(max_workers=len(targets)) as ex:
            res = list(ex.map(timed, targets))
        print(f"\n[{grp}] {sum(1 for ok, _ in res if ok)}/{len(targets)}  "
              f"(метод: {CFG['check_method']}, таймаут {CFG['check_timeout']} с)")
        for t, (ok, ms) in zip(targets, res):
            print(f"  {'+' if ok else '-'} {t.host:<28} {ms} мс")

    print("\n=== Реальный интернет мимо туннеля (Яндекс DNS по физ. адаптеру) ===")
    print("OK" if physical_probe(loc["physical"]) else "НЕТ ОТВЕТА")


if __name__ == "__main__":
    if "--net" in sys.argv:
        cli_net("--watch" in sys.argv)
    elif "--check" in sys.argv:
        cli_check()
    else:
        if GUI_ERR is not None:
            print("Не хватает библиотек для виджета:", GUI_ERR)
            sys.exit(1)
        Application().run()