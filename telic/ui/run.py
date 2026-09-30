"""Running UI lemmas: find each lemma's app, start it, learn its model at each
viewport, check, and cache the verdicts by exactly what they depend on (the
app's sources, the ``[ui]`` config, the lemma, and telic's UI code)."""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
import time
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any, Callable

from .app import App, AppError, build_digest
from .check import Atoms, ModelCheck, Occlusion, Outcome, combine, hit_test
from .config import ConfigError, UiConfig, find, load
from .driver import DriverError
from .spec import SKIP_DIRS, SOURCE_EXT, Scan, UiDecl, UiLemma

CACHE = os.path.join(".telic", "ui.json")
AUTO_STATES = 100
VERSION = 1


@dataclass
class UiResult:
    lemma: UiLemma
    app: str  # the telic.toml it ran under ('' when none)
    status: str  # proved | refuted | open | vacuous
    method: str = ""
    detail: str = ""
    trace: list[str] | None = None
    replay: dict[str, Any] | None = None
    viewports: list[dict[str, Any]] = field(default_factory=list)
    cached: bool = False

    def to_json(self) -> dict[str, Any]:
        lem = self.lemma
        return {
            "name": lem.name,
            "at": f"{lem.path}:{lem.line}",
            "property": lem.text,
            "aims": list(lem.aims),
            "via": lem.via,
            "app": self.app,
            "status": self.status,
            "method": self.method,
            "detail": self.detail,
            "trace": self.trace,
            "replay": self.replay,
            "viewports": self.viewports,
            "cached": self.cached,
        }


@dataclass
class UiApp:
    config: str
    url: str = ""
    models: list[dict[str, Any]] = field(default_factory=list)
    error: str | None = None
    seconds: float = 0.0
    cached: bool = False


@dataclass
class UiReport:
    apps: list[UiApp] = field(default_factory=list)
    results: list[UiResult] = field(default_factory=list)
    decls: list[UiDecl] = field(default_factory=list)
    problems: list[tuple[str, int, str]] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {
            "apps": [{"config": a.config, "url": a.url, "error": a.error, "cached": a.cached, "seconds": round(a.seconds, 1), "models": a.models} for a in self.apps],
            "lemmas": [r.to_json() for r in self.results],
            "problems": [{"file": p, "line": ln, "message": m} for p, ln, m in self.problems],
        }


_TOOL: str | None = None


def tool_digest() -> str:
    global _TOOL
    if _TOOL is None:
        h = hashlib.sha256(str(VERSION).encode())
        for f in sorted(Path(__file__).parent.glob("*.py")):
            h.update(f.name.encode() + f.read_bytes())
        _TOOL = h.hexdigest()[:16]
    return _TOOL


def _stderr_log(prefix: str) -> Callable[[str], None]:
    if not sys.stderr.isatty():
        return lambda _m: None

    def log(m: str) -> None:
        sys.stderr.write(f"\r\033[K{prefix}{m}")
        sys.stderr.flush()

    return log


def run(sc: Scan, root: str, enabled: bool = True, log: Callable[[str], None] | None = None) -> UiReport:
    rep = UiReport(decls=list(sc.aims))
    groups: dict[str | None, list[UiLemma]] = {}
    for lem in sc.lemmas:
        if lem.problem:
            rep.problems.append((lem.path, lem.line, lem.problem))
            rep.results.append(UiResult(lem, "", "open", "", lem.problem))
            continue
        groups.setdefault(find(os.path.join(root, lem.path), root), []).append(lem)
    cache_path = os.path.join(root, CACHE)
    try:
        cache = json.loads(Path(cache_path).read_text())
        if cache.get("version") != VERSION:
            cache = {}
    except (OSError, ValueError):
        cache = {}
    entries: dict[str, Any] = cache.get("entries", {})
    used: set[str] = set()
    for cfg_path, lems in groups.items():
        if cfg_path is None:
            for lem in lems:
                why = f"no telic.toml with a [ui] section at or above {os.path.dirname(lem.path) or '.'}: add one that says how to start the app"
                rep.results.append(UiResult(lem, "", "open", "", why))
            continue
        try:
            cfg = load(cfg_path, root)
        except ConfigError as e:
            rel = os.path.relpath(cfg_path, root)
            rep.problems.append((rel, 1, str(e)))
            rep.results += [UiResult(lem, rel, "open", "", str(e)) for lem in lems]
            continue
        base = f"{tool_digest()}:{build_digest(cfg)}:{cfg.digest()}"
        keys = {lem.name: hashlib.sha256(f"{base}:{lem.name}:{lem.text}".encode()).hexdigest()[:24] for lem in lems}
        app = UiApp(cfg.path)
        rep.apps.append(app)
        todo = []
        for lem in lems:
            hit = entries.get(keys[lem.name])
            if hit is not None:
                used.add(keys[lem.name])
                r = _result(lem, cfg.path, hit["result"])
                r.cached = True
                rep.results.append(r)
                app.models = app.models or hit.get("models", [])
                app.url = app.url or hit.get("url", "")
            else:
                todo.append(lem)
        app.cached = not todo
        if not todo:
            continue
        if not enabled:
            rep.results += [UiResult(lem, cfg.path, "open", "", "not run (--no-ui)") for lem in todo]
            continue
        t0 = time.monotonic()
        got = run_app(cfg, todo, app, log or _stderr_log(f"telic ui {cfg.path}: "))
        app.seconds = time.monotonic() - t0
        if log is None and sys.stderr.isatty():
            sys.stderr.write("\r\033[K")
        for lem in todo:
            r = got[lem.name]
            rep.results.append(r)
            if app.error is None:
                entries[keys[lem.name]] = {"result": r.to_json(), "models": app.models, "url": app.url}
                used.add(keys[lem.name])
    keep = {k: v for k, v in entries.items() if k in used}
    try:
        os.makedirs(os.path.dirname(cache_path), exist_ok=True)
        Path(cache_path).write_text(json.dumps({"version": VERSION, "entries": keep}, indent=1, sort_keys=True))
    except OSError:
        pass
    order = {id(lem): i for i, lem in enumerate(sc.lemmas)}
    rep.results.sort(key=lambda r: order.get(id(r.lemma), 0))
    return rep


def _result(lem: UiLemma, app: str, d: dict[str, Any]) -> UiResult:
    #@ requires "status" in d
    return UiResult(lem, app, d["status"], d.get("method", ""), d.get("detail", ""), d.get("trace"), d.get("replay"), d.get("viewports", []))


def run_app(cfg: UiConfig, lems: list[UiLemma], app: UiApp, log: Callable[[str], None]) -> dict[str, UiResult]:
    """Each viewport is learned in its own browser, side by side."""
    from concurrent.futures import ThreadPoolExecutor

    try:
        with App(cfg, log) as url:
            app.url = url
            atoms = Atoms(lems)
            seeds = propose(cfg, lems) if cfg.seed else None
            jobs = list(enumerate(cfg.viewports))
            with ThreadPoolExecutor(max_workers=len(jobs)) as pool:
                done = list(pool.map(lambda job: _viewport(cfg, url, lems, atoms, seeds, job[0], job[1], log), jobs))
    except (AppError, DriverError) as e:
        app.error = str(e)
        return {lem.name: UiResult(lem, cfg.path, "open", "", f"the app did not run: {e}") for lem in lems}
    outs: dict[str, list[Outcome]] = {lem.name: [] for lem in lems}
    for model, got in done:
        app.models.append(model)
        for name, o in got.items():
            outs[name].append(o)
    out: dict[str, UiResult] = {}
    for lem in lems:
        o = combine(outs[lem.name])
        out[lem.name] = UiResult(lem, cfg.path, o.status, o.method, o.detail, o.trace, o.replay, [x.to_json() for x in outs[lem.name]])
    return out


def _viewport(cfg: UiConfig, url: str, lems: list[UiLemma], atoms: Atoms, seeds, i: int, size: tuple[int, int], log) -> tuple[dict[str, Any], dict[str, Outcome]]:
    from .learn import Explorer
    from .web import WebDriver

    w, h = size
    vp = f"{w}x{h}"
    drivers = []
    try:
        for _ in range(max(1, cfg.settings.workers)):
            d = WebDriver(url, settle_ms=cfg.settle_ms)
            drivers.append(d)
            d.start()
            d.viewport(w, h)
        occluding = [lem for lem in lems if lem.prop and lem.prop.kind == "unobscured"]

        def learn(settings):
            occl = {lem.name: Occlusion() for lem in occluding}
            holder: list[Explorer] = []

            def probe(state, snap, driver):
                for lem in occluding:
                    p = lem.prop
                    if not p.cond.eval(snap, holder[0].model.home):
                        continue
                    n, bad = hit_test(driver, p.goal, snap)
                    occl[lem.name].rendered[state.id] = n
                    if n and bad:
                        occl[lem.name].covered[state.id] = bad

            ex = Explorer(drivers, atoms.preds, settings, vp, probe, lambda m: log(f"{vp}: {m}"))
            holder.append(ex)
            return ex, ex.learn(seeds), occl

        s = cfg.settings
        if s.abstraction == "auto":
            # the exact abstraction when the app is small enough for it; else screens
            ex, model, occl = learn(replace(s, abstraction="controls", max_states=min(s.max_states, AUTO_STATES)))
            if "state budget" in model.stop:
                ex, model, occl = learn(replace(s, abstraction="screens", max_seconds=max(1.0, s.max_seconds - model.seconds)))
                model.notes.insert(0, f"states are screens: telling controls apart gave more than {AUTO_STATES} states (set [ui] abstraction to choose)")
        else:
            ex, model, occl = learn(s)
        dialogs = sum(d.dialogs for d in drivers)
        if dialogs:
            model.notes.append(f"{dialogs} browser dialogs (alert, confirm) were accepted")
        _dump(cfg, model)
        mc = ModelCheck(ex, atoms, occl, cfg.witnesses)
        got: dict[str, Outcome] = {}
        for lem in lems:
            got[lem.name] = mc.persists(lem) if lem.prop.kind == "persists" else mc.check(lem)
        return model.summary(), got
    finally:
        for d in drivers:
            d.stop()


def _dump(cfg: UiConfig, model) -> None:
    """The learned model, next to the app: .telic/ui-model-<viewport>.json."""
    try:
        d = os.path.join(cfg.dir, ".telic")
        os.makedirs(d, exist_ok=True)
        Path(d, f"ui-model-{model.viewport}.json").write_text(json.dumps(model.dump(), indent=1, ensure_ascii=False))
    except OSError:
        pass


# ---------------------------------------------------------------------------
# An oracle's model of the app, from its source: a seed, tested like any guess


def propose(cfg: UiConfig, lems: list[UiLemma], budget: int = 40000) -> list[list[str]] | None:
    from .. import oracle

    files: dict[str, str] = {}
    size = 0
    for dirpath, dirnames, filenames in os.walk(cfg.dir):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS and not d.startswith("."))
        for f in sorted(filenames):
            if not f.endswith(SOURCE_EXT) or f.endswith((".config.js", ".config.ts")):
                continue
            try:
                text = Path(dirpath, f).read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                continue
            if size + len(text) > budget:
                continue
            files[os.path.relpath(os.path.join(dirpath, f), cfg.dir)] = text
            size += len(text)
    state = {"sources": files, "lemmas": [f"{lem.name}: {lem.text}" for lem in lems]}
    questions = {
        "paths": {
            "type": "text",
            "instructions": (
                "Read the app's source and predict how a user moves through it. Answer with only a JSON array of action sequences, "
                "each an array of steps written as an accessible role and name, e.g. [[\"button \\\"Settings\\\"\", \"checkbox \\\"Dark mode\\\"\"], "
                "[\"link \\\"About\\\"\", \"key Escape\"]]. Cover every screen, dialog and menu, and the states the lemmas mention."
            ),
        }
    }
    got = oracle.consult("ui-model", state, questions, root=cfg.dir)
    text = (got.answers.get("paths") or {}).get("text")
    if not text:
        return None
    m = re.search(r"\[.*\]", text, re.S)
    try:
        data = json.loads(m.group(0)) if m else None
    except ValueError:
        return None
    if not isinstance(data, list):
        return None
    return [[str(x) for x in p] for p in data if isinstance(p, list)][:40]
