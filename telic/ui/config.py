"""The ``[ui]`` section of ``telic.toml``: how to start the app and how far to explore.

    [ui]
    command = "npm run dev -- --port {port}"   # or: static = "dist" (served by telic),
    build = "npm run build"                    #  or: url = "http://..." (already running)
    url = "http://127.0.0.1:{port}/"           # with static: the path to open, e.g. "/app/"
    viewports = ["390x844", "1280x800"]
    routes = ["/groups/:id"]                   # route patterns: each names one screen
    max_states = 300
    max_depth = 30

An iOS app runs in the iOS Simulator, one device at a time:

    [ui]
    platform = "ios"
    app = "build/Notes.app"                    # after 'build'; or: project/workspace + scheme
    build = "sh build.sh"                      #  (telic runs xcodebuild)
    devices = ["iPhone 17", "iPad Air 11-inch (M3)"]
    launch_args = ["-UITesting", "YES"]

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
    witnesses: int = 20
    settle_ms: int = 50
    platform: str = "web"
    app: str | None = None  # ios: the .app bundle, relative to dir
    project: str | None = None
    workspace: str | None = None
    scheme: str | None = None
    devices: list[str] = field(default_factory=list)  # ios: device types; empty: the newest plain iPhone
    launch_args: list[str] = field(default_factory=list)
    wait: float = 5.0  # seconds: a timer the app sets for up to this long is waited for, like any action
    routes: list[str] = field(default_factory=list)  # web: route patterns that name screens, e.g. "/groups/:id"

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
        "url", "command", "static", "build", "ready_timeout", "viewports", "max_states", "max_depth", "max_actions", "max_seconds", "walks",
        "walk_length", "workers", "abstraction", "text", "fill", "keys", "ignore", "driver", "inputs", "witnesses", "settle_ms", "wait",
        "platform", "app", "project", "workspace", "scheme", "devices", "launch_args",
        "walk_seed", "routes",
    }
    unknown = sorted(set(ui) - known)
    if unknown:
        raise ConfigError(f"{os.path.relpath(path, root)}: unknown [ui] key{'s' * (len(unknown) > 1)} {', '.join(unknown)} (known: {', '.join(sorted(known))})")
    platform = str(ui.get("platform", "web"))
    if platform not in ("web", "ios"):
        raise ConfigError(f"{os.path.relpath(path, root)}: [ui] platform is \"web\" (the default) or \"ios\"")
    if platform == "ios":
        if not (ui.get("app") or (ui.get("scheme") and (ui.get("project") or ui.get("workspace")))):
            raise ConfigError(f"{os.path.relpath(path, root)}: [ui] platform \"ios\" needs 'app' (a .app bundle, made by 'build') or 'scheme' with 'project' or 'workspace'")
        if "viewports" in ui:
            raise ConfigError(f"{os.path.relpath(path, root)}: on iOS the screen is the device's: list device types in 'devices', not 'viewports'")
    elif not (ui.get("url") or ui.get("command") or ui.get("static")):
        raise ConfigError(f"{os.path.relpath(path, root)}: [ui] needs 'command' (starts the app), 'static' (a directory telic serves) or 'url' (an app already running)")
    s = Settings()
    for k in ("max_states", "max_depth", "max_actions", "walks", "walk_length", "workers"):
        if k in ui:
            setattr(s, k, int(ui[k]))
    if "walk_seed" in ui:
        s.seed = int(ui["walk_seed"])
    if "max_seconds" in ui:
        s.max_seconds = float(ui["max_seconds"])
    if "text" in ui:
        s.text = str(ui["text"])
    if "keys" in ui:
        s.keys = tuple(str(k) for k in ui["keys"])
    if "ignore" in ui:
        s.ignore = tuple(str(k) for k in ui["ignore"])
    if "abstraction" in ui:
        if ui["abstraction"] not in ("auto", "controls", "screens"):
            raise ConfigError(f"{os.path.relpath(path, root)}: [ui] abstraction is \"auto\" (the default), \"controls\" or \"screens\"")
        s.abstraction = ui["abstraction"]
    if "fill" in ui:
        if not isinstance(ui["fill"], dict):
            raise ConfigError(f"{os.path.relpath(path, root)}: [ui] fill is a table of field-name regex = value, e.g. fill = {{ Email = \"me@example.com\" }}")
        s.fill = tuple((str(k), str(v)) for k, v in ui["fill"].items())
    routes = ui.get("routes", [])
    if not isinstance(routes, list) or not all(isinstance(r, str) and r.startswith("/") for r in routes):
        raise ConfigError(f"{os.path.relpath(path, root)}: [ui] routes is a list of route patterns, e.g. routes = [\"/groups/:id\"]")
    cfg = UiConfig(
        dir=os.path.dirname(os.path.abspath(path)),
        routes=[str(r) for r in routes],
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
        witnesses=int(ui.get("witnesses", 20)),
        settle_ms=int(ui.get("settle_ms", 50)),
        platform=platform,
        app=ui.get("app"),
        project=ui.get("project"),
        workspace=ui.get("workspace"),
        scheme=ui.get("scheme"),
        devices=[str(d) for d in ui.get("devices", [])],
        launch_args=[str(a) for a in ui.get("launch_args", [])],
        wait=float(ui.get("wait", 5)),
    )
    if "viewports" in ui:
        cfg.viewports = [_size(v) for v in ui["viewports"]]
        if not cfg.viewports:
            raise ConfigError(f"{cfg.path}: viewports is empty; list at least one, e.g. [\"390x844\"]")
    if cfg.driver != "web":
        raise ConfigError(f"{cfg.path}: driver {cfg.driver!r} is not available (only 'web' so far)")
    return cfg
