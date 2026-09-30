"""Starting the app under test: build it, serve it or run its dev server, and wait until it answers."""

from __future__ import annotations

import functools
import hashlib
import http.server
import os
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator

from .config import UiConfig
from .spec import SKIP_DIRS


class AppError(Exception):
    pass


_LIVE: set[App] = set()  # apps whose server is up, for a signal to take down

# Runs the dev server command in its own process group and takes the whole
# group down when telic's end of its stdin closes: whenever telic exits, even
# killed outright, nothing it started outlives it.
_GUARD = """
import os, signal, subprocess, sys, threading
p = subprocess.Popen(sys.argv[1], shell=True, stdin=subprocess.DEVNULL)
def down(*_):
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    try:
        os.killpg(0, signal.SIGTERM)
        p.wait(timeout=5)
    except (OSError, subprocess.TimeoutExpired):
        pass
    os.killpg(0, signal.SIGKILL)
signal.signal(signal.SIGTERM, down)
threading.Thread(target=lambda: (sys.stdin.buffer.read(), os.kill(os.getpid(), signal.SIGTERM)), daemon=True).start()
code = p.wait()
signal.signal(signal.SIGTERM, signal.SIG_IGN)
os.killpg(0, signal.SIGTERM)
os._exit(code if code >= 0 else 128 - code)
"""


@contextmanager
def torn_down_on_signals() -> Iterator[None]:
    """On SIGTERM or SIGINT, stop every dev server this process started, then
    die of the signal as before. Browsers go with the process (their driver
    exits when its pipe to this process closes); servers run in their own
    session, so they would not."""
    if threading.current_thread() is not threading.main_thread():
        yield
        return

    def handler(sig, _frame) -> None:
        for app in list(_LIVE):
            app.kill()
        signal.signal(sig, signal.SIG_DFL)
        os.kill(os.getpid(), sig)

    old = {s: signal.signal(s, handler) for s in (signal.SIGTERM, signal.SIGINT)}
    try:
        yield
    finally:
        for s, h in old.items():
            signal.signal(s, h)


def free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def answers(url: str) -> bool:
    try:
        with urllib.request.urlopen(url, timeout=2) as r:
            return r.status < 500
    except urllib.error.HTTPError as e:
        return e.code < 500
    except (OSError, ValueError):
        return False


OUTPUT = {"dist", "build", "target", "coverage"}  # build output where the app's top level has it; elsewhere, sources


def build_digest(cfg: UiConfig) -> str:
    """What the app is built from: every file under its directory (or the
    configured ``inputs``), except dependencies, caches and build output
    (unless the build output is what telic serves). An app telic does not
    start is also what its page serves now."""
    h = hashlib.sha256()
    if cfg.url and not cfg.command and not cfg.static:
        try:
            with urllib.request.urlopen(cfg.url, timeout=5) as r:
                h.update(r.read())
        except (OSError, ValueError) as e:
            h.update(f"unreachable: {e}".encode())
    roots = [os.path.join(cfg.dir, p) for p in cfg.inputs] if cfg.inputs else [cfg.dir]
    if cfg.static and not cfg.build and not cfg.inputs:
        roots.append(os.path.join(cfg.dir, cfg.static))
    files: list[str] = []
    for top in roots:
        if os.path.isfile(top):
            files.append(top)
            continue
        for dirpath, dirnames, filenames in os.walk(top):
            dirnames[:] = sorted(d for d in dirnames if not d.startswith(".") and (d not in SKIP_DIRS or (d in OUTPUT and dirpath != cfg.dir)))
            files += [os.path.join(dirpath, f) for f in sorted(filenames)]
    for f in files:
        try:
            data = Path(f).read_bytes()
        except OSError:
            continue
        h.update(os.path.relpath(f, cfg.dir).encode() + b"\0" + hashlib.sha256(data).digest())
    return h.hexdigest()[:16]


class _Quiet(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args) -> None:
        pass

    def send_head(self):
        path = self.translate_path(self.path)
        if not os.path.exists(path) and "." not in os.path.basename(self.path.split("?")[0]):
            self.path = "/index.html"  # a single-page app routes on the client
        return super().send_head()


class App:
    """``with App(cfg) as url:`` the app is up at ``url`` until the block ends."""

    def __init__(self, cfg: UiConfig, log=None):
        self.cfg = cfg
        self.log = log or (lambda _m: None)
        self.proc: subprocess.Popen | None = None
        self.server: http.server.ThreadingHTTPServer | None = None
        self.out = tempfile.TemporaryFile()

    def __enter__(self) -> str:
        try:
            return self._start()
        except BaseException:
            self.__exit__(None, None, None)
            raise

    def _start(self) -> str:
        cfg = self.cfg
        if cfg.build:
            self.log(f"building: {cfg.build}")
            p = subprocess.run(cfg.build, shell=True, cwd=cfg.dir, capture_output=True, text=True)
            if p.returncode != 0:
                tail = (p.stderr or p.stdout).strip().splitlines()[-3:]
                raise AppError(f"'{cfg.build}' failed (exit {p.returncode}): {' | '.join(tail)}")
        if cfg.platform == "ios":
            return self._ios_app()
        if cfg.static:
            root = os.path.join(cfg.dir, cfg.static)
            if not os.path.isdir(root):
                raise AppError(f"static directory {cfg.static!r} does not exist in {cfg.dir}")
            self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), functools.partial(_Quiet, directory=root))
            threading.Thread(target=self.server.serve_forever, daemon=True).start()
            base = f"http://127.0.0.1:{self.server.server_address[1]}/"
            return base + (cfg.url or "").lstrip("/")
        if cfg.command:
            port = free_port()
            url = (cfg.url or "http://127.0.0.1:{port}/").replace("{port}", str(port))
            cmd = cfg.command.replace("{port}", str(port))
            self.log(f"starting: {cmd}")
            env = dict(os.environ, PORT=str(port), BROWSER="none")
            self.proc = subprocess.Popen(
                [sys.executable, "-c", _GUARD, cmd], cwd=cfg.dir, env=env, stdin=subprocess.PIPE, stdout=self.out, stderr=subprocess.STDOUT, start_new_session=True
            )
            _LIVE.add(self)
            deadline = time.monotonic() + cfg.ready_timeout
            while time.monotonic() < deadline:
                if answers(url):
                    return url
                if self.proc.poll() is not None:
                    raise AppError(f"'{cmd}' exited ({self.proc.returncode}) before {url} answered: {self._tail()}")
                time.sleep(0.2)
            raise AppError(f"{url} did not answer within {cfg.ready_timeout:.0f}s of '{cmd}': {self._tail()}")
        url = cfg.url or ""
        if not answers(url):
            raise AppError(f"nothing answers at {url}: start the app, or give [ui] a 'command' or 'static'")
        return url

    def _ios_app(self) -> str:
        """The .app bundle: 'app' as built, or what xcodebuild makes of the scheme."""
        cfg = self.cfg
        if cfg.app:
            app = os.path.join(cfg.dir, cfg.app)
            if not os.path.isfile(os.path.join(app, "Info.plist")):
                raise AppError(f"{cfg.app} is not an app bundle in {cfg.dir}{' (did build make it?)' if cfg.build else ': add a build command'}")
            return app
        derived = os.path.join(cfg.dir, ".telic", "DerivedData")
        which = ["-workspace", cfg.workspace] if cfg.workspace else ["-project", cfg.project or ""]
        cmd = ["xcodebuild", *which, "-scheme", cfg.scheme or "", "-sdk", "iphonesimulator", "-configuration", "Debug", "-derivedDataPath", derived, "-jobs", "4", "build"]
        self.log(f"building: {' '.join(cmd)}")
        p = subprocess.run(cmd, cwd=cfg.dir, capture_output=True, text=True, check=False)
        if p.returncode != 0:
            errors = [x.strip() for x in p.stdout.splitlines() if "error:" in x] or (p.stderr or p.stdout).strip().splitlines()[-3:]
            raise AppError(f"xcodebuild failed (exit {p.returncode}): {' | '.join(errors[:3])}")
        products = os.path.join(derived, "Build", "Products", "Debug-iphonesimulator")
        apps = sorted(f for f in os.listdir(products) if f.endswith(".app")) if os.path.isdir(products) else []
        if not apps:
            raise AppError(f"xcodebuild made no .app in {products}")
        return os.path.join(products, f"{cfg.scheme}.app" if f"{cfg.scheme}.app" in apps else apps[0])

    def _tail(self) -> str:
        self.out.seek(0)
        lines = [x.strip() for x in self.out.read().decode(errors="replace").splitlines() if x.strip()]
        errors = [x for x in lines if "error" in x.lower()]
        return (errors[0] if errors else " | ".join(lines[-3:]))[:300] or "no output"

    def kill(self) -> None:
        """Stop the dev server and everything it started."""
        _LIVE.discard(self)
        if self.proc is not None and self.proc.stdin is not None:
            self.proc.stdin.close()
        if self.proc is not None and self.proc.poll() is None:
            try:
                os.killpg(self.proc.pid, signal.SIGTERM)
                self.proc.wait(timeout=5)
            except (ProcessLookupError, subprocess.TimeoutExpired, PermissionError):
                try:
                    os.killpg(self.proc.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    pass

    def __exit__(self, *exc) -> None:
        self.kill()
        if self.server is not None:
            self.server.shutdown()
            self.server.server_close()
        self.out.close()
