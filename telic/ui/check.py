"""Checking UI lemmas against a learned model, and confirming in the app.

What each verdict rests on is said with it:

- reachability and invariants are *tested on the learned model* (its size,
  whether exploration finished, and how conformance testing went are shown);
  a route the model promises is replayed in the app before it counts;
- ``reachable`` is tested with a witness replayed in the app;
- occlusion is hit-tested in every reachable state where the element renders;
- persistence is tested by changing the control and reopening the app.

A counterexample is always a replayable action trace, replayed in the app
before it is reported. A property that no reachable state makes relevant is
vacuous, never passed.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any

from .driver import DriverError
from .learn import Explorer, Model, UiState, Worker
from .spec import TRUE, Pred, Prop, Target, UiLemma
from .tree import Node, Snapshot, controls, value_of


@dataclass
class Outcome:
    status: str  # tested | refuted | open | vacuous
    method: str  # learned model | witness replayed | hit-tested | tested
    detail: str
    viewport: str = ""
    trace: list[str] | None = None
    replay: dict[str, Any] | None = None
    relevant: int = 0

    def to_json(self) -> dict[str, Any]:
        return {k: v for k, v in self.__dict__.items() if v is not None}


@dataclass
class Occlusion:
    """Hit-test results gathered at every visit to a state, while exploring,
    testing the model and replaying routes."""

    rendered: dict[int, int] = field(default_factory=dict)
    covered: dict[int, list[str]] = field(default_factory=dict)
    paths: dict[int, list[list[str]]] = field(default_factory=dict)  # ways a covered visit got there, shortest first
    tests: int = 0

    def record(self, sid: int, n: int, bad: list[str], paths: list[list[str]]) -> None:
        self.tests += 1
        self.rendered[sid] = max(n, self.rendered.get(sid, 0))
        if n and bad:
            self.covered.setdefault(sid, bad)
            known = self.paths.setdefault(sid, [])
            known += [p for p in paths if p not in known]
            known.sort(key=len)
            del known[4:]


def hit_test(driver, t: Target, snap: Snapshot) -> tuple[int, list[str]]:
    rendered, bad = 0, []
    for n in t.find(snap):
        if n.ref is None:
            continue
        try:
            shown, points = driver.uncovered(n)
        except DriverError:
            continue
        if not shown:
            continue
        rendered += 1
        for where, who in points:
            if who is not None:
                bad.append(f"{n.label}: {where} is covered by {who}")
    return rendered, bad


class Atoms:
    """The predicates of every lemma, in the order the explorer keeps them."""

    def __init__(self, lemmas: list[UiLemma]):
        self.preds: list[Pred] = []
        self.index: dict[str, int] = {}
        for lem in lemmas:
            if lem.prop is not None:
                for p in lem.prop.atoms():
                    self.add(p)

    def add(self, p: Pred) -> None:
        k = str(p)
        if k not in self.index:
            self.index[k] = len(self.preds)
            self.preds.append(p)

    def holds(self, p: Pred, s: UiState) -> bool:
        return p is TRUE or s.atoms[self.index[str(p)]]


def _phrase(p: Pred) -> str:
    return "true" if p is TRUE else str(p)


class ModelCheck:
    def __init__(self, ex: Explorer, atoms: Atoms, occl: dict[str, Occlusion], witnesses: int = 20):
        self.ex = ex
        self.w = ex.main
        self.m: Model = ex.model
        self.atoms = atoms
        self.occl = occl
        self.witnesses = witnesses

    # -- replay -------------------------------------------------------------

    def replay(self, sigs: list[str], w: Worker | None = None) -> tuple[Snapshot | None, list[str], str]:
        """Run ``sigs`` from a fresh start in the app: (final snapshot or
        None, what was done, why it stopped)."""
        w = w or self.w
        try:
            self.ex.reset(w)
        except DriverError as e:
            return None, [], str(e)
        done: list[str] = []
        for sig in sigs:
            a = w.acts.get(sig)
            if a is None or w.cur is None:
                return None, done, f"step {len(done) + 1} ({sig}) is not offered"
            done.append(a.label)
            at = w.cur
            if self.ex.fire(w, at, sig) is None:
                return None, done, f"step {len(done)} failed: {at.blocked.get(sig, 'blocked')}"
        return w.snap, done, ""

    def reach(self, path: list[str], goals: set[int], goal: Pred, w: Worker, budget: int = 0) -> tuple[bool, str]:
        """Follow ``path`` in the app, then get to a goal state, re-planning on
        the model from wherever the app actually is after each step (so state
        the abstraction does not see cannot fake a route)."""
        snap, _, why = self.replay(path, w)
        if snap is None:
            return False, why
        # One state of the model can be several in the app (two dialogs that
        # look alike): each step is taken once from each screen as the app
        # shows it, so a route that leads back round is not taken again.
        used: dict[str, set[str]] = {}
        for _ in range(budget or 3 * (len(self.m.states) + 2)):
            if goal.eval(w.snap, self.m.home):
                return True, ""
            at = w.cur
            if at is None:
                return False, "the app left the model"
            here = used.setdefault(_concrete(w), set())
            avoid = {(at.id, sig) for sig in here | (set(at.actions) - set(w.acts))}
            route = self.m.path(at.id, goals, avoid=avoid)
            if not route:
                return False, f"no route left from {at.describe()}"
            sig = route[0]
            here.add(sig)
            if self.ex.fire(w, at, sig) is None and w.cur is None:
                return False, f"{at.labels.get(sig, sig)} failed in {at.describe()}"
        return False, "gave up after too many steps"

    def trace_of(self, s: UiState) -> list[str]:
        out, cur = [], self.m.states[0]
        for sig in s.access:
            out.append(cur.labels.get(sig, sig))
            nxt = sorted(self.m.trans.get(cur.id, {}).get(sig, ()))
            cur = self.m.states[nxt[0]] if nxt else cur
        return out

    def _stopped(self) -> str:
        return f"exploration is incomplete: {self.m.stop}" if self.m.stop else ""

    def _nothing(self, method: str, what: str) -> Outcome:
        """Absence from the learned graph is not evidence of source behavior."""
        return Outcome("open", method, f"model-only: {what}; no source refinement establishes that the learned graph is complete ({self._size()})")

    def _size(self) -> str:
        return f"{len(self.m.states)} states" + ("" if self.m.complete else f", {self._stopped()}")

    # -- properties ----------------------------------------------------------

    def check(self, lem: UiLemma) -> Outcome:
        p = lem.prop
        assert p is not None
        out = {
            "always_reachable": self.always_reachable,
            "reachable": self.reachable,
            "always": self.invariant,
            "never": self.invariant,
            "unobscured": self.unobscured,
        }[p.kind](p, lem)
        out.viewport = self.m.viewport
        return self._blind(out) if p.kind != "reachable" else out

    def _blind(self, out: Outcome) -> Outcome:
        """A proof over every state rests on the model seeing what decides
        what renders: when the source names state it could not read, the
        model may have merged states the app keeps apart."""
        if (self.m.unread or self.m.unpressed) and out.status in ("tested", "vacuous"):
            what = "tested" if out.status == "tested" else "vacuous"
            why = []
            if self.m.unread:
                why.append(f"it cannot see {', '.join(self.m.unread[:3])}: handlers change it and it decides what renders")
            if self.m.unpressed:
                why.append(f"it cannot tell which keys to press: {', '.join(self.m.unpressed[:3])}")
            return Outcome("open", out.method, f"{what} on the model, but {'; and '.join(why)} ({out.detail})", out.viewport, out.trace, out.replay, out.relevant)
        return out

    def _states(self, p: Pred) -> list[UiState]:
        return [s for s in self.m.states if self.atoms.holds(p, s)]

    def always_reachable(self, p: Prop, lem: UiLemma) -> Outcome:
        assert isinstance(p.goal, Pred)
        goals = {s.id for s in self._states(p.goal)}
        rel = self._states(p.cond)
        if not rel:
            return self._nothing("learned model", f"no reachable state has {_phrase(p.cond)}")
        can = self.m.reaching(goals)
        bad = sorted((s for s in rel if s.id not in can), key=lambda s: (s.depth, s.id))
        if bad:
            s = bad[0]
            n = len(s.actions)
            if not self.m.closed_from(s.id):
                return Outcome("open", "learned model", f"no route to {_phrase(p.goal)} found from {s.describe()}, but exploration from there is unfinished", relevant=len(rel))
            snap, done, why = self.replay(s.access)
            if snap is None or self.w.cur is None or self.w.cur.id != s.id:
                return Outcome("open", "learned model", f"stuck at {s.describe()} in the model, but its path did not replay ({why or 'reached a different state'})", trace=self.trace_of(s), relevant=len(rel))
            blocked = sorted(set(s.blocked.values()))
            tail = f"; {len(s.blocked)} blocked ({blocked[0]})" if blocked else ""
            return Outcome(
                "open",
                "learned model",
                f"model-only: no route to {_phrase(p.goal)} was found from {s.describe()} among its {n} observed actions{tail}; the learned graph does not establish that no route exists",
                trace=done,
                replay={"confirmed": True, "summary": f"reached {s.describe()}"},
                relevant=len(rel),
            )
        forced = self.m.forcing(goals)
        chancy = sorted((s for s in rel if s.id not in forced), key=lambda s: (s.depth, s.id))
        if chancy:
            s = chancy[0]
            return Outcome(
                "open",
                "learned model",
                f"every route from {s.describe()} to {_phrase(p.goal)} takes a step with more than one observed outcome "
                f"({self.m.nondeterministic} such transitions: the app has state the abstraction does not see)",
                trace=self.trace_of(s),
                relevant=len(rel),
            )
        if not self.m.complete:
            return Outcome("open", "learned model", f"every {len(rel)} relevant state can reach it, but {self._stopped()}", relevant=len(rel))
        # Replay the escape routes the model promises: from every way into each
        # state seen, since one state of the model can be several in the app.
        todo = [s for s in sorted(rel, key=lambda s: (s.depth, s.id)) if s.id not in goals]
        picked = todo[: self.witnesses]
        paths = [(s, s.access) for s in picked]
        for s in picked:
            seen = {tuple(s.access)}
            for alt in [s.history] + [self.m.states[q].access + [sig] for q, m in sorted(self.m.trans.items()) for sig, ts in sorted(m.items()) if s.id in ts and q != s.id]:
                if alt and tuple(alt) not in seen:
                    seen.add(tuple(alt))
                    paths.append((s, alt))
        paths = paths[: 3 * self.witnesses]
        queue = list(reversed(paths))
        failed: list[tuple[UiState, list[str], str]] = []

        def work(w: Worker) -> None:
            while True:
                with self.ex.lock:
                    if not queue or failed:
                        return
                    s, path = queue.pop()
                ok, why = self.reach(path, goals, p.goal, w)
                if not ok:
                    with self.ex.lock:
                        failed.append((s, path, why))

        self.ex._pool(work)
        if failed:
            s, path, why = failed[0]
            return Outcome("open", "learned model", f"the model's route from {s.describe()} to {_phrase(p.goal)} did not replay in the app ({why})", trace=self.m.labels(path), relevant=len(rel))
        extra = f"; routes replayed along {len(paths)} path{'s' * (len(paths) != 1)} into {len(picked)}/{len(todo)} states" if todo else ""
        return Outcome("tested", "learned model", f"{len(rel)} relevant of {self._size()}{extra}", relevant=len(rel))

    def reachable(self, p: Prop, lem: UiLemma) -> Outcome:
        assert isinstance(p.goal, Pred)
        goals = sorted(self._states(p.goal), key=lambda s: (s.depth, s.id))
        if not goals:
            if self.m.complete:
                return Outcome("open", "learned model", f"model-only: no reachable state with {_phrase(p.goal)} was observed; the learned graph does not establish that no such state exists ({self._size()})")
            return Outcome("open", "learned model", f"not reached in {self._size()}, and {self._stopped()}")
        s = goals[0]
        snap, done, why = self.replay(s.access)
        if snap is not None and p.goal.eval(snap, self.m.home):
            return Outcome("tested", "witness replayed", f"reached in {len(done)} step{'s' * (len(done) != 1)}", trace=done, replay={"confirmed": True, "summary": f"reached {s.describe()}"}, relevant=len(goals))
            return Outcome("open", "learned model", f"the model reaches it, but the path did not replay ({why or 'ended elsewhere'})", trace=self.trace_of(s))

    def invariant(self, p: Prop, lem: UiLemma) -> Outcome:
        assert isinstance(p.goal, Pred)
        rel = self._states(p.cond)
        if not rel:
            return self._nothing("learned model", f"no reachable state has {_phrase(p.cond)}")
        good = (lambda s: self.atoms.holds(p.goal, s)) if p.kind == "always" else (lambda s: not self.atoms.holds(p.goal, s))
        bad = sorted((s for s in rel if not good(s)), key=lambda s: (s.depth, s.id))
        if bad:
            s = bad[0]
            snap, done, why = self.replay(s.access)
            holds = snap is not None and p.cond.eval(snap, self.m.home) and (p.goal.eval(snap, self.m.home) != (p.kind == "always"))
            what = f"{_phrase(p.goal)} is {'false' if p.kind == 'always' else 'true'}" + (f" while {_phrase(p.cond)}" if p.cond is not TRUE else "")
            if holds:
                return Outcome("refuted", "learned model", f"{what} at {s.describe()}", trace=done, replay={"confirmed": True, "summary": what}, relevant=len(rel))
            return Outcome("open", "learned model", f"{what} at {s.describe()} in the model, but it did not replay ({why or 'not seen again'})", trace=self.trace_of(s), relevant=len(rel))
        if not self.m.complete:
            return Outcome("open", "learned model", f"holds in all {len(rel)} relevant states found, but {self._stopped()}", relevant=len(rel))
        return Outcome("tested", "learned model", f"holds in {len(rel)} relevant of {self._size()}", relevant=len(rel))

    def unobscured(self, p: Prop, lem: UiLemma) -> Outcome:
        t = p.goal
        assert isinstance(t, Target)
        o = self.occl.get(lem.name) or Occlusion()
        rendered = [self.m.states[i] for i, n in o.rendered.items() if n]
        if not rendered:
            return self._nothing("hit-tested", f"{t} never renders{'' if p.cond is TRUE else ' while ' + _phrase(p.cond)}")
        bad = sorted((self.m.states[i] for i in o.covered), key=lambda s: (s.depth, s.id))
        tests = f" ({o.tests} hit-tests)"
        if bad:
            s = bad[0]
            for path in [s.access] + [alt for alt in o.paths.get(s.id, []) if alt != s.access]:
                snap, done, why = self.replay(path)
                again = hit_test(self.w.d, t, snap)[1] if snap is not None else []
                if again:
                    break
            if again:
                return Outcome(
                    "refuted",
                    "hit-tested",
                    f"covered in {len(bad)}/{len(rendered)} states where it renders; at {s.describe()}: {again[0]}",
                    trace=done,
                    replay={"confirmed": True, "summary": again[0]},
                    relevant=len(rendered),
                )
            return Outcome("open", "hit-tested", f"covered at {s.describe()} while exploring ({o.covered[s.id][0]}), but not when replayed ({why or 'uncovered'})", trace=self.m.labels((o.paths.get(s.id) or [s.access])[0]), relevant=len(rendered))
        if not self.m.complete:
            return Outcome("open", "hit-tested", f"uncovered in {len(rendered)}/{len(rendered)} states found where it renders{tests}, but {self._stopped()}", relevant=len(rendered))
        return Outcome("tested", "hit-tested", f"uncovered in {len(rendered)}/{len(rendered)} states where it renders{tests}", relevant=len(rendered))

    # -- persistence -----------------------------------------------------------

    def persists(self, lem: UiLemma) -> Outcome:
        p = lem.prop
        assert p is not None and isinstance(p.goal, Target)
        t = p.goal
        enabled = Pred("is", (t, "enabled"))
        cands = sorted(self._states(enabled), key=lambda s: (s.depth, s.id))
        if not cands:
            out = self._nothing("tested", f"{t} is never shown enabled")
            out.viewport = self.m.viewport
            return self._blind(out)
        s = cands[0]
        snap, done, why = self.replay(s.access)
        if snap is None:
            return Outcome("open", "tested", f"could not reach {t} again ({why})", trace=self.trace_of(s), viewport=self.m.viewport)
        node = _enabled(t, snap)
        if node is None:
            return Outcome("open", "tested", f"{t} was not enabled when replayed", trace=done, viewport=self.m.viewport)
        before = value_of(node)
        change = _change(node)
        if change is None:
            return Outcome("open", "tested", f"telic cannot change a {node.role}", viewport=self.m.viewport)
        kind, arg, what = change
        from .tree import Action

        try:
            self.w.d.do(Action(kind, "persist", what, node.ref, arg))
            after_snap = self.ex.look(self.w)
        except DriverError as e:
            return Outcome("open", "tested", f"could not change {t}: {e}", trace=done, viewport=self.m.viewport)
        n2 = _enabled(t, after_snap) or next(iter(t.find(after_snap)), None)
        after = value_of(n2) if n2 is not None else None
        if after is None or after == before:
            return Outcome("open", "tested", f"{what} did not change its value ({before!r})", trace=done + [what], viewport=self.m.viewport)
        back: list[str] = []
        try:
            self.w.d.reopen()
            snap = self.ex.look(self.w)
            self.w.cur = None
            if not _enabled(t, snap):
                # the app reopens somewhere the model knows: go on from there; else from the start
                at = self.ex.known(snap, self.w.d)
                goals = {c.id for c in cands}
                route = self.m.path(at.id, goals) if at is not None else None
                for sig in route if route is not None else s.access:
                    a = self.w.acts.get(sig)
                    if a is None:
                        raise DriverError(f"after reopening, '{sig}' is not offered")
                    back.append(a.label)
                    self.w.d.do(a)
                    self.ex.look(self.w)
        except DriverError as e:
            return Outcome("open", "tested", f"after reopening the app, could not get back to {t}: {e}", trace=done + [what, "reopen the app"] + back, viewport=self.m.viewport)
        n3 = next(iter(t.find(self.w.snap)), None) if self.w.snap is not None else None
        again = value_of(n3) if n3 is not None else None
        steps = done + [what, "reopen the app"] + back
        if again == after:
            return Outcome("tested", "tested", f"changed it ({before} → {after}), reopened the app: still {after}", trace=steps, viewport=self.m.viewport, relevant=1)
        return Outcome(
            "refuted",
            "tested",
            f"changed it ({before} → {after}), reopened the app: {again if again is not None else 'gone'}",
            trace=steps,
            replay={"confirmed": True, "summary": f"{t} was {again} after reopening"},
            viewport=self.m.viewport,
            relevant=1,
        )


def _concrete(w: Worker) -> str:
    """The screen as the app shows it now, finer than any abstraction: what can be done and every control's state."""
    snap = w.snap
    if snap is None:
        return ""
    return json.dumps([snap.screen, snap.overlays(), sorted(w.acts), controls(snap), snap.hidden], sort_keys=True, default=str)


def _enabled(t: Target, snap: Snapshot) -> Node | None:
    return next((n for n in t.find(snap) if "disabled" not in n.states and n.ref is not None), None)


def _change(n: Node) -> tuple[str, str | None, str] | None:
    if n.role in ("checkbox", "switch", "radio", "menuitemcheckbox", "menuitemradio", "button", "tab", "option"):
        return "click", None, f"click {n.label}"
    if n.role == "combobox":
        opts = [c.name for c in n.children if c.role == "option" and "selected" not in c.states and "disabled" not in c.states]
        if opts:
            return "select", opts[0], f"choose {opts[0]!r} in {n.label}"
        return "fill", "telic persisted", f"type into {n.label}"
    if n.role in ("textbox", "searchbox"):
        return "fill", (n.value or "") + " telic", f"type into {n.label}"
    if n.role in ("slider", "spinbutton"):
        return "press", "ArrowRight" if n.role == "slider" else "ArrowUp", f"increase {n.label}"
    return None


def combine(outs: list[Outcome]) -> Outcome:
    #@ requires len(outs) > 0
    """One verdict over every viewport: refuted anywhere is refuted; a tested
    result needs no open viewport and at least one that was not vacuous."""
    for st in ("refuted", "open"):
        hit = [o for o in outs if o.status == st]
        if hit:
            o = hit[0]
            return Outcome(st, o.method, f"at {o.viewport}: {o.detail}" if len(outs) > 1 else o.detail, o.viewport, o.trace, o.replay, o.relevant)
    tested = [o for o in outs if o.status == "tested"]
    proved = [o for o in outs if o.status == "proved"]
    status = "tested" if tested else "proved" if proved else "vacuous"
    evidence = tested or proved or outs
    first = evidence[0]
    return Outcome(status, first.method, _per_viewport(outs), "", first.trace, first.replay, sum(o.relevant for o in evidence))


def _per_viewport(outs: list[Outcome]) -> str:
    """'x (at 390x844, 1280x800)' when every viewport says the same, else each in turn."""
    if len(outs) == 1:
        return outs[0].detail
    if len({o.detail for o in outs}) == 1:
        return f"{outs[0].detail} (at {', '.join(o.viewport for o in outs)})"
    return "; ".join(f"at {o.viewport}: {o.detail}" for o in outs)
