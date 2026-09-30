"""Starting the app under test: build it, serve it or run its dev server, and wait until it answers."""

from __future__ import annotations

import functools
import hashlib
import http.server
import os
import signal
import socket
import subprocess
import tempfile
import threading
import time
import urllib.error
import urllib.request
from pathlib import Path

from .config import UiConfig
from .spec import SKIP_DIRS


class AppError(Exception):
    pass


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


def build_digest(cfg: UiConfig) -> str:
    """What the app is built from: every file under its directory (or the
    configured ``inputs``), except dependencies, caches and build output
    (unless the build output is what telic serves)."""
    h = hashlib.sha256()
    roots = [os.path.join(cfg.dir, p) for p in cfg.inputs] if cfg.inputs else [cfg.dir]
    if cfg.static and not cfg.build and not cfg.inputs:
        roots.append(os.path.join(cfg.dir, cfg.static))
    files: list[str] = []
    for top in roots:
        if os.path.isfile(top):
            files.append(top)
            continue
        for dirpath, dirnames, filenames in os.walk(top):
            dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS and not d.startswith("."))
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
            self.proc = subprocess.Popen(cmd, shell=True, cwd=cfg.dir, env=env, stdout=self.out, stderr=subprocess.STDOUT, start_new_session=True)
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

    def _tail(self) -> str:
        self.out.seek(0)
        lines = self.out.read().decode(errors="replace").strip().splitlines()
        return " | ".join(lines[-3:]) or "no output"

    def __exit__(self, *exc) -> None:
        if self.proc is not None and self.proc.poll() is None:
            try:
                os.killpg(self.proc.pid, signal.SIGTERM)
                self.proc.wait(timeout=5)
            except (ProcessLookupError, subprocess.TimeoutExpired, PermissionError):
                try:
                    os.killpg(self.proc.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    pass
        if self.server is not None:
            self.server.shutdown()
            self.server.server_close()
        self.out.close()
