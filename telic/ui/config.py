"""The ``[ui]`` section of ``telic.toml``: how to start the app and how far to explore.

    [ui]
    command = "npm run dev -- --port {port}"   # or: static = "dist" (served by telic),
    build = "npm run build"                    #  or: url = "http://..." (already running)
    url = "http://127.0.0.1:{port}/"           # with static: the path to open, e.g. "/app/"
    viewports = ["390x844", "1280x800"]
    max_states = 150
    max_depth = 12

The nearest ``telic.toml`` with a ``[ui]`` section above a lemma's file is
the app that lemma is about.
"""

from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass, field
from typing import Any

from .learn import Settings

NAME = "telic.toml"


class ConfigError(Exception):
    pass


@dataclass
class UiConfig:
    dir: str  # absolute
    path: str  # the telic.toml, relative to the root
    raw: dict[str, Any]
    url: str | None = None
    command: str | None = None
    static: str | None = None
    build: str | None = None
    ready_timeout: float = 60.0
    viewports: list[tuple[int, int]] = field(default_factory=lambda: [(390, 844), (1280, 800)])
    settings: Settings = field(default_factory=Settings)
    driver: str = "web"
    inputs: list[str] | None = None
    seed: bool = False
    witnesses: int = 20
    settle_ms: int = 50

    def digest(self) -> str:
        return hashlib.sha256(json.dumps(self.raw, sort_keys=True, default=str).encode()).hexdigest()[:16]


def _toml(path: str) -> dict[str, Any]:
    try:
        import tomllib  # type: ignore[import-not-found]
    except ImportError:  # Python 3.10
        import tomli as tomllib  # type: ignore[no-redef]
    with open(path, "rb") as fh:
        return tomllib.load(fh)


def find(start: str, root: str) -> str | None:
    """The nearest telic.toml with a [ui] section at or above ``start``, within ``root``."""
    d = os.path.abspath(start if os.path.isdir(start) else os.path.dirname(start))
    top = os.path.abspath(root)
    while True:
        f = os.path.join(d, NAME)
        if os.path.exists(f):
            try:
                if "ui" in _toml(f):
                    return f
            except (OSError, ValueError):
                return f
        if d == top or not d.startswith(top) or os.path.dirname(d) == d:
            return None
        d = os.path.dirname(d)


def _size(v: Any) -> tuple[int, int]:
    try:
        w, h = str(v).lower().split("x")
        return int(w), int(h)
    except ValueError:
        raise ConfigError(f"viewport {v!r}: write WIDTHxHEIGHT, e.g. \"390x844\"") from None


def load(path: str, root: str) -> UiConfig:
    try:
        data = _toml(path)
    except (OSError, ValueError) as e:
        raise ConfigError(f"{os.path.relpath(path, root)}: {e}") from None
    ui = data.get("ui")
    if not isinstance(ui, dict):
        raise ConfigError(f"{os.path.relpath(path, root)} has no [ui] section")
    known = {
        "url", "command", "static", "build", "ready_timeout", "viewports", "max_states", "max_depth", "max_seconds", "walks",
        "walk_length", "workers", "text", "keys", "ignore", "driver", "inputs", "seed", "witnesses", "settle_ms",
    }
    unknown = sorted(set(ui) - known)
    if unknown:
        raise ConfigError(f"{os.path.relpath(path, root)}: unknown [ui] key{'s' * (len(unknown) > 1)} {', '.join(unknown)} (known: {', '.join(sorted(known))})")
    if not (ui.get("url") or ui.get("command") or ui.get("static")):
        raise ConfigError(f"{os.path.relpath(path, root)}: [ui] needs 'command' (starts the app), 'static' (a directory telic serves) or 'url' (an app already running)")
    s = Settings()
    for k in ("max_states", "max_depth", "walks", "walk_length", "workers"):
        if k in ui:
            setattr(s, k, int(ui[k]))
    if "max_seconds" in ui:
        s.max_seconds = float(ui["max_seconds"])
    if "text" in ui:
        s.text = str(ui["text"])
    if "keys" in ui:
        s.keys = tuple(str(k) for k in ui["keys"])
    if "ignore" in ui:
        s.ignore = tuple(str(k) for k in ui["ignore"])
    cfg = UiConfig(
        dir=os.path.dirname(os.path.abspath(path)),
        path=os.path.relpath(path, root),
        raw=ui,
        url=ui.get("url"),
        command=ui.get("command"),
        static=ui.get("static"),
        build=ui.get("build"),
        ready_timeout=float(ui.get("ready_timeout", 60)),
        settings=s,
        driver=str(ui.get("driver", "web")),
        inputs=list(ui["inputs"]) if "inputs" in ui else None,
        seed=bool(ui.get("seed", False)),
        witnesses=int(ui.get("witnesses", 20)),
        settle_ms=int(ui.get("settle_ms", 50)),
    )
    if "viewports" in ui:
        cfg.viewports = [_size(v) for v in ui["viewports"]]
    if cfg.driver != "web":
        raise ConfigError(f"{cfg.path}: driver {cfg.driver!r} is not available (only 'web' so far)")
    return cfg
