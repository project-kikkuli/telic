"""Running UI lemmas: find each lemma's app, start it, learn its model at each
viewport, test, and cache the observations by what they depend on (the
app's sources, the ``[ui]`` config, the lemma, and telic's UI code)."""

from __future__ import annotations

import hashlib
import json
import os
import shlex
import sys
import time
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any, Callable
from urllib.parse import unquote, urlsplit

from . import slots, source, static
from .app import App, AppError, build_digest, torn_down_on_signals
from .check import Atoms, ModelCheck, Occlusion, Outcome, combine, hit_test
from .config import ConfigError, UiConfig, find, load
from .driver import DriverError
from .spec import Pred, Scan, UiDecl, UiLemma

CACHE = os.path.join(".telic", "ui.json")
AUTO_STATES = 100
VERSION = 1


@dataclass
class UiResult:
    lemma: UiLemma
    app: str  # the telic.toml it ran under ('' when none)
    status: str  # tested | refuted | open | vacuous
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
        for f in [*sorted(Path(__file__).parent.glob("*.py")), Path(__file__).parent.parent / "frontend" / "ts" / "uiscan.mjs"]:
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
    static_models: dict[tuple[str, str, str | None], tuple[dict[str, Any] | None, str | None, str | None]] = {}
    for cfg_path, lems in groups.items():
        if cfg_path is None:
            for lem in lems:
                top = os.path.dirname(os.path.join(root, lem.path)) or root
                r = _static_result(lem, "", top, root, entries, used, static_models, configured=False)
                rep.results.append(r)
            continue
        try:
            cfg = load(cfg_path, root)
        except ConfigError as e:
            rel = os.path.relpath(cfg_path, root)
            rep.problems.append((rel, 1, str(e)))
            rep.results += [UiResult(lem, rel, "open", "", str(e)) for lem in lems]
            continue
        # route patterns the lemmas name also name screens: every lemma's model depends on them
        cfg = replace(cfg, routes=route_patterns(cfg.routes, lems))
        base = f"{tool_digest()}:{build_digest(cfg)}:{cfg.digest()}:{','.join(cfg.routes)}"
        keys = {lem.name: hashlib.sha256(f"{base}:{lem.name}:{lem.text}".encode()).hexdigest()[:24] for lem in lems}
        app = UiApp(cfg.path)
        rep.apps.append(app)
        todo = []
        pipeline = "vite-react" if cfg.command and not cfg.build and not cfg.static and not cfg.inputs and _verified_vite_command(cfg.command) else None
        source_top = cfg.dir if pipeline else None
        html_entry = _static_html_entry(cfg, source_top) if source_top else None
        for lem in lems:
            source_result = _static_result(lem, cfg.path, source_top, root, entries, used, static_models, configured=source_top is not None, html_entry=html_entry, pipeline=pipeline, config_path=os.path.join(root, cfg.path) if pipeline else None, command=cfg.command if pipeline else None, config_digest=cfg.digest() if pipeline else None)
            if source_result is not None:
                rep.results.append(source_result)
                continue
            hit = entries.get(keys[lem.name])
            if hit is not None:
                used.add(keys[lem.name])
                r = _result(lem, cfg.path, hit["result"])
                r.cached = True
                rep.results.append(r)
                app.models = app.models or hit.get("models", [])
                app.url = app.url or hit.get("url", "")
                entries[keys[lem.name]] = {**hit, "result": r.to_json()}
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


def _static_html_entry(cfg: UiConfig, top: str) -> str | None:
    raw = urlsplit(cfg.url or "")
    if raw.query or raw.fragment:
        return None
    if raw.scheme or raw.netloc:
        if (raw.scheme != "http" or raw.hostname not in ("127.0.0.1", "localhost")
                or "{port}" not in raw.netloc or raw.path not in ("", "/")):
            return None
    path = unquote(raw.path).lstrip("/")
    if ".." in Path(path).parts:
        return None
    if not path:
        return "index.html"
    target = os.path.join(top, path)
    if path.endswith("/") or os.path.isdir(target):
        return os.path.join(path, "index.html")
    if os.path.isfile(target):
        return path
    if "." not in os.path.basename(path):
        return "index.html"
    return path


def _verified_vite_command(command: str) -> bool:
    try:
        args = tuple(shlex.split(command))
    except ValueError:
        return False
    forms = {
        ("npx", "vite", "--port", "{port}"),
        ("npx", "vite", "--port", "{port}", "--strictPort"),
        ("npx", "vite", "--port", "{port}", "--strictPort", "--host", "127.0.0.1"),
        ("npx", "vite", "--port", "{port}", "--host", "127.0.0.1"),
    }
    return args in forms


def _static_result(lem: UiLemma, app: str, top: str | None, root: str, entries: dict[str, Any], used: set[str], extracted: dict[tuple[str, str, str | None], tuple[dict[str, Any] | None, str | None, str | None]], configured: bool, html_entry: str | None = None, pipeline: str | None = None, config_path: str | None = None, command: str | None = None, config_digest: str | None = None) -> UiResult | None:
    if top is None or html_entry is None and configured:
        return None
    entry = html_entry or "index.html"
    cache_key = (top, entry, f"{pipeline}:{config_digest}" if pipeline else None)
    if cache_key not in extracted:
        extracted[cache_key] = static.extract(top, root, entry, pipeline, config_path=config_path, command=command, config_digest=config_digest)
    model, identity, why = extracted[cache_key]
    if model is None:
        if configured:
            return None
        return UiResult(lem, app, "open", "source model", why or "the app has no statically extractable source model")
    outcome = static.check(model, identity or "", lem)
    if configured and outcome.method != "source proof":
        return None
    result = UiResult(lem, app, outcome.status, outcome.method, outcome.detail, outcome.trace, {"source": outcome.source, "receipt": outcome.receipt})
    if outcome.receipt:
        key = hashlib.sha256(f"{tool_digest()}:{identity}:{lem.name}:{lem.text}".encode()).hexdigest()
        entries[key] = {"result": result.to_json(), "source_receipt": outcome.receipt}
        used.add(key)
    return result


def route_patterns(declared: list[str], lems: list[UiLemma]) -> list[str]:
    """The [ui] routes, then the route patterns lemmas name (``screen
    "/groups/:id"``), most specific first: a pattern names the screens it matches."""
    named = [str(p.args[0]) for lem in lems if lem.prop is not None for p in lem.prop.atoms() if p.op == "screen" and ":" in str(p.args[0])]
    pats = list(dict.fromkeys([*declared, *named]))
    return sorted(pats, key=lambda p: (-sum(1 for x in p.split("/") if x and not x.startswith(":") and x != "*"), pats.index(p)))


def _result(lem: UiLemma, app: str, d: dict[str, Any]) -> UiResult:
    #@ requires "status" in d
    status = d["status"]
    raw_method = d.get("method")
    result_method = ""
    source_proof = False
    learned_model = False
    if isinstance(raw_method, str):
        result_method = "cached observation" if raw_method in ("source proof", "static proof") else raw_method
        learned_model = raw_method in ("learned model",)
    detail = d.get("detail", "")
    if d["status"] == "proved" and not source_proof:
        status = "tested"
        detail = detail.replace("proved", "tested")
    if d["status"] == "vacuous" and not source_proof:
        status = "open"
        detail = "model-only: " + detail
    if d["status"] == "refuted" and learned_model and lem.prop is not None and lem.prop.kind in ("reachable", "always_reachable"):
        status = "open"
        detail = "model-only: " + detail
    viewports = []
    default_method = d.get("method")
    for v in d.get("viewports", []):
        verdict = v.get("status")
        raw_method = v.get("method", default_method)
        source_proof = False
        learned_model = False
        if isinstance(raw_method, str):
            source_proof = False
            learned_model = raw_method in ("learned model",)
        if verdict == "proved" and not source_proof:
            verdict = "tested"
        elif (verdict == "vacuous" and not source_proof) or (verdict == "refuted" and learned_model and lem.prop is not None and lem.prop.kind in ("reachable", "always_reachable")):
            verdict = "open"
        viewport = {**v, "status": verdict}
        if raw_method in ("source proof", "static proof"):
            viewport["method"] = "cached observation"
        viewports.append(viewport)
    return UiResult(lem, app, status, result_method, detail, d.get("trace"), d.get("replay"), viewports)


def run_app(cfg: UiConfig, lems: list[UiLemma], app: UiApp, log: Callable[[str], None]) -> dict[str, UiResult]:
    """Each viewport is learned in its own browser, side by side."""
    from concurrent.futures import ThreadPoolExecutor

    try:
        with torn_down_on_signals(), App(cfg, log) as url:
            app.url = url
            atoms = Atoms(lems)
            facts = source.scan(cfg.dir, cfg.platform)
            if facts.keys:
                cfg = replace(cfg, settings=replace(cfg.settings, keys=tuple(dict.fromkeys([*cfg.settings.keys, *(k.key for k in facts.keys)]))))
            # one simulator at a time: each device is learned after the last
            jobs = list(enumerate(cfg.viewports if cfg.platform == "web" else cfg.devices or [""]))
            with ThreadPoolExecutor(max_workers=len(jobs) if cfg.platform == "web" else 1) as pool:
                done = list(pool.map(lambda job: _viewport(cfg, url, lems, atoms, facts, job[0], job[1], log), jobs))
    except (AppError, DriverError) as e:
        app.error = str(e)
        return {lem.name: UiResult(lem, cfg.path, "open", "", f"the app did not run: {e}") for lem in lems}
    outs: dict[str, list[Outcome]] = {lem.name: [] for lem in lems}
    for models, got in done:
        app.models += models
        for name, o in got.items():
            outs[name].append(o)
    out: dict[str, UiResult] = {}
    for lem in lems:
        o = combine(outs[lem.name])
        out[lem.name] = UiResult(lem, cfg.path, o.status, o.method, o.detail, o.trace, o.replay, [x.to_json() for x in outs[lem.name]])
    return out


def _viewport(cfg: UiConfig, url: str, lems: list[UiLemma], atoms: Atoms, facts, i: int, size: tuple[int, int] | str, log) -> tuple[list[dict[str, Any]], dict[str, Outcome]]:
    # one browser (or simulator) slot each, machine-wide: runs in other processes queue for them
    vp = f"{size[0]}x{size[1]}" if isinstance(size, tuple) else size or "iOS"
    with slots.hold(max(1, cfg.settings.workers) if cfg.platform == "web" else 1, log=lambda m: log(f"{vp}: {m}")) as n:
        return _learn(cfg, url, lems, atoms, facts, size, n, log)


def _learn(cfg: UiConfig, url: str, lems: list[UiLemma], atoms: Atoms, facts, size: tuple[int, int] | str, browsers: int, log) -> tuple[list[dict[str, Any]], dict[str, Outcome]]:
    from .learn import Explorer

    drivers: list = []
    try:
        if cfg.platform == "ios":
            from . import sim
            from .ios import IosDriver

            vp = str(size) or sim.default_device()
            d = IosDriver(url, vp, launch_args=cfg.launch_args, settle_ms=cfg.settle_ms)
            drivers.append(d)
            d.start()
        else:
            from .web import WebDriver

            w, h = size  # type: ignore[misc]
            vp = f"{w}x{h}"
            for _ in range(browsers):
                d = WebDriver(url, settle_ms=cfg.settle_ms, wait_ms=int(cfg.wait * 1000), routes=tuple(cfg.routes))
                drivers.append(d)
                d.start()
                d.viewport(w, h)
        occluding = [lem for lem in lems if lem.prop and lem.prop.kind == "unobscured"]

        def learn(group: list[UiLemma], atoms: Atoms, settings):
            occl = {lem.name: Occlusion() for lem in occluding if lem in group}
            holder: list[Explorer] = []

            def probe(state, snap, driver, paths):
                for lem in occluding:
                    p = lem.prop
                    if lem.name in occl and p.cond.eval(snap, holder[0].model.home):
                        occl[lem.name].record(state.id, *hit_test(driver, p.goal, snap), paths)

            ex = Explorer(drivers, atoms.preds, settings, vp, probe, lambda m: log(f"{vp}: {m}"))
            holder.append(ex)
            return ex, ex.learn(), occl

        got: dict[str, Outcome] = {}
        summaries = []
        for group, watched in _cones(lems, facts):
            gatoms = Atoms(group)
            for d in drivers:
                d.read = set()
                d.watch(watched)
            s = cfg.settings
            if s.abstraction == "auto":
                # the exact abstraction when the app is small enough for it; else screens
                ex, model, occl = learn(group, gatoms, replace(s, abstraction="controls", max_states=min(s.max_states, AUTO_STATES)))
                if "state budget" in model.stop:
                    ex, model, occl = learn(group, gatoms, replace(s, abstraction="screens", max_seconds=max(1.0, s.max_seconds - model.seconds)))
                    model.notes.insert(0, f"states are screens: telling controls apart gave more than {AUTO_STATES} states (set [ui] abstraction to choose)")
            else:
                ex, model, occl = learn(group, gatoms, s)
            dialogs = sum(getattr(d, "dialogs", 0) for d in drivers)
            if dialogs:
                model.notes.append(f"{dialogs} browser dialogs (alert, confirm) were accepted")
            _source_notes(model, facts, watched, set().union(*(d.read for d in drivers)))
            if len(group) < len(lems):
                model.lemmas = [lem.name for lem in group]
            _dump(cfg, model)
            mc = ModelCheck(ex, gatoms, occl, cfg.witnesses)
            for lem in group:
                got[lem.name] = mc.persists(lem) if lem.prop.kind == "persists" else mc.check(lem)
            summaries.append(model.summary())
        return summaries, got
    finally:
        for d in drivers:
            d.stop()


def _observes_content(lem: UiLemma) -> bool:
    """Does the lemma look at what the tree shows of an element (a name, a
    state, a value, where it is drawn), not only at which elements exist?"""
    p = lem.prop
    if p is None or p.kind in ("unobscured", "persists"):
        return True

    def content(x) -> bool:
        if not isinstance(x, Pred):
            return False
        if x.op == "overlay":
            return bool(x.args)
        if x.op in ("is", "eq"):
            return True
        if x.op == "present":
            t = x.args[0]
            return t.name is not None or t.pattern is not None
        return any(content(a) for a in x.args if isinstance(a, Pred))

    return content(p.goal) or content(p.cond)


def _cones(lems: list[UiLemma], facts) -> list[tuple[list[UiLemma], list]]:
    """The lemmas in groups that can share a model, each with the state the
    model must read: what can change what its lemmas observe. Every lemma
    watches the state that decides which elements exist (and so which
    actions there are); only one that looks at names, states or values
    watches the state that decides only those."""
    every = list(facts.hidden)
    shaped = [h for h in every if "structure" in h.affects]
    if len(shaped) == len(every):
        return [(lems, every)]
    blind = [lem for lem in lems if not _observes_content(lem)]
    seeing = [lem for lem in lems if _observes_content(lem)]
    return [(g, w) for g, w in ((blind, shaped), (seeing, every)) if g]


def _source_notes(model, facts, watched, read: set[str]) -> None:
    """What the source added to the model, and what it says the model cannot see."""
    if facts.keys:
        model.keys = [f"{k.key} ({k.at()})" for k in facts.keys]
        model.notes.insert(0, "keys found in the source: " + ", ".join(model.keys))
    model.hidden = [h.describe() for h in watched if f"{h.path}:{h.name}" in read]
    model.unread = [h.describe() for h in watched if f"{h.path}:{h.name}" not in read]
    if model.hidden:
        model.notes.append(f"state the tree does not show, read from the app: {', '.join(h.name for h in watched if f'{h.path}:{h.name}' in read)}")
    if model.unread:
        model.notes.insert(0, f"cannot read {', '.join(model.unread)} from the app: handlers change it and it decides what renders")
    clocked = [h for h in watched if h.clock]
    if clocked:
        model.notes.append("also changed by timers, not waited for: " + ", ".join(f"{h.describe()}, timer at line {', '.join(map(str, h.clock))}" for h in clocked))
    if facts.gaps:
        model.unpressed = [g.describe() for g in facts.gaps]
        model.notes.insert(0, "key handlers react to keys the source does not spell out: " + ", ".join(model.unpressed))
    for e in facts.errors[:3]:
        model.notes.append(e)


def _dump(cfg: UiConfig, model) -> None:
    """The learned model, next to the app: .telic/ui-model-<viewport>.json
    (-<lemmas> when it is for some of them)."""
    try:
        d = os.path.join(cfg.dir, ".telic")
        os.makedirs(d, exist_ok=True)
        tail = f"-{'+'.join(model.lemmas)}"[:80] if model.lemmas else ""
        Path(d, f"ui-model-{model.viewport}{tail}.json").write_text(json.dumps(model.dump(), indent=1, ensure_ascii=False))
    except OSError:
        pass
