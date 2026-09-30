"""Checking UI lemmas against a learned model, and confirming in the app.

What each verdict rests on is said with it:

- reachability and invariants are *proved on the learned model* (its size,
  whether exploration finished, and how conformance testing went are shown);
  a route the model promises is replayed in the app before it counts;
- ``reachable`` is proved by a witness replayed in the app;
- occlusion is hit-tested in every reachable state where the element renders;
- persistence is tested by changing the control and reopening the app.

A counterexample is always a replayable action trace, replayed in the app
before it is reported. A property that no reachable state makes relevant is
vacuous, never passed.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from .driver import DriverError
from .learn import Explorer, Model, UiState, Worker
from .spec import TRUE, Pred, Prop, Target, UiLemma
from .tree import Node, Snapshot, value_of


@dataclass
class Outcome:
    status: str  # proved | refuted | open | vacuous
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
    """Hit-test results gathered while exploring, per state."""

    rendered: dict[int, int] = field(default_factory=dict)
    covered: dict[int, list[str]] = field(default_factory=dict)


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

    def trace_of(self, s: UiState) -> list[str]:
        out, cur = [], self.m.states[0]
        for sig in s.access:
            out.append(cur.labels.get(sig, sig))
            nxt = sorted(self.m.trans.get(cur.id, {}).get(sig, ()))
            cur = self.m.states[nxt[0]] if nxt else cur
        return out

    def _stopped(self) -> str:
        return f"exploration stopped at the {self.m.stop}" if self.m.stop else ""

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
        return out

    def _states(self, p: Pred) -> list[UiState]:
        return [s for s in self.m.states if self.atoms.holds(p, s)]

    def always_reachable(self, p: Prop, lem: UiLemma) -> Outcome:
        assert isinstance(p.goal, Pred)
        goals = {s.id for s in self._states(p.goal)}
        rel = self._states(p.cond)
        if not rel:
            return Outcome("vacuous", "learned model", f"no reachable state has {_phrase(p.cond)} ({self._size()})")
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
                "refuted",
                "learned model",
                f"stuck at {s.describe()}: none of its {n} actions leads to {_phrase(p.goal)}{tail}",
                trace=done,
                replay={"confirmed": True, "summary": f"reached {s.describe()}"},
                relevant=len(rel),
            )
        if not self.m.complete:
            return Outcome("open", "learned model", f"every {len(rel)} relevant state can reach it, but {self._stopped()}", relevant=len(rel))
        # Replay the escape routes the model promises.
        todo = [s for s in sorted(rel, key=lambda s: (s.depth, s.id)) if s.id not in goals][: self.witnesses]
        routes = {s.id: self.m.path(s.id, goals) or [] for s in todo}
        queue = list(reversed(todo))
        failed: list[tuple[UiState, str]] = []

        def work(w: Worker) -> None:
            while True:
                with self.ex.lock:
                    if not queue or failed:
                        return
                    s = queue.pop()
                snap, _, why = self.replay(s.access + routes[s.id], w)
                if snap is None or not p.goal.eval(snap, self.m.home):
                    with self.ex.lock:
                        failed.append((s, why or "ended elsewhere"))

        self.ex._pool(work)
        if failed:
            s, why = failed[0]
            return Outcome("open", "learned model", f"the model's route from {s.describe()} to {_phrase(p.goal)} did not replay in the app ({why})", trace=self.trace_of(s), relevant=len(rel))
        extra = f"; routes replayed from {len(todo)}/{len(todo)} states" if todo else ""
        return Outcome("proved", "learned model", f"{len(rel)} relevant of {self._size()}{extra}", relevant=len(rel))

    def reachable(self, p: Prop, lem: UiLemma) -> Outcome:
        assert isinstance(p.goal, Pred)
        goals = sorted(self._states(p.goal), key=lambda s: (s.depth, s.id))
        if not goals:
            if self.m.complete:
                return Outcome("refuted", "learned model", f"no reachable state has {_phrase(p.goal)} in the complete model ({self._size()})")
            return Outcome("open", "learned model", f"not reached in {self._size()}, and {self._stopped()}")
        s = goals[0]
        snap, done, why = self.replay(s.access)
        if snap is not None and p.goal.eval(snap, self.m.home):
            return Outcome("proved", "witness replayed", f"reached in {len(done)} step{'s' * (len(done) != 1)}", trace=done, replay={"confirmed": True, "summary": f"reached {s.describe()}"}, relevant=len(goals))
        return Outcome("open", "learned model", f"the model reaches it, but the path did not replay ({why or 'ended elsewhere'})", trace=self.trace_of(s))

    def invariant(self, p: Prop, lem: UiLemma) -> Outcome:
        assert isinstance(p.goal, Pred)
        rel = self._states(p.cond)
        if not rel:
            return Outcome("vacuous", "learned model", f"no reachable state has {_phrase(p.cond)} ({self._size()})")
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
        return Outcome("proved", "learned model", f"holds in {len(rel)} relevant of {self._size()}", relevant=len(rel))

    def unobscured(self, p: Prop, lem: UiLemma) -> Outcome:
        t = p.goal
        assert isinstance(t, Target)
        o = self.occl.get(lem.name) or Occlusion()
        rendered = [self.m.states[i] for i, n in o.rendered.items() if n]
        if not rendered:
            return Outcome("vacuous", "hit-tested", f"{t} never renders{'' if p.cond is TRUE else ' while ' + _phrase(p.cond)} ({self._size()})")
        bad = sorted((self.m.states[i] for i in o.covered), key=lambda s: (s.depth, s.id))
        if bad:
            s = bad[0]
            snap, done, why = self.replay(s.access)
            again = hit_test(self.w.d, t, snap)[1] if snap is not None else []
            if again:
                return Outcome(
                    "refuted",
                    "hit-tested",
                    f"covered in {len(bad)}/{len(rendered)} states where it renders; at {s.describe()}: {again[0]}",
                    trace=done,
                    replay={"confirmed": True, "summary": again[0]},
                    relevant=len(rendered),
                )
            return Outcome("open", "hit-tested", f"covered at {s.describe()} while exploring ({o.covered[s.id][0]}), but not when replayed ({why or 'uncovered'})", trace=self.trace_of(s), relevant=len(rendered))
        if not self.m.complete:
            return Outcome("open", "hit-tested", f"uncovered in {len(rendered)}/{len(rendered)} states found where it renders, but {self._stopped()}", relevant=len(rendered))
        return Outcome("proved", "hit-tested", f"uncovered in {len(rendered)}/{len(rendered)} states where it renders", relevant=len(rendered))

    # -- persistence -----------------------------------------------------------

    def persists(self, lem: UiLemma) -> Outcome:
        p = lem.prop
        assert p is not None and isinstance(p.goal, Target)
        t = p.goal
        enabled = Pred("is", (t, "enabled"))
        cands = sorted(self._states(enabled), key=lambda s: (s.depth, s.id))
        if not cands:
            return Outcome("vacuous", "tested", f"{t} is never shown enabled ({self._size()})", viewport=self.m.viewport)
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
        try:
            self.w.d.reopen()
            self.ex.look(self.w)
            self.w.cur = None
            for sig in s.access:
                a = self.w.acts.get(sig)
                if a is None:
                    raise DriverError(f"after reopening, '{sig}' is not offered")
                self.w.d.do(a)
                self.ex.look(self.w)
        except DriverError as e:
            return Outcome("open", "tested", f"after reopening the app, could not get back to {t}: {e}", trace=done + [what, "reopen the app"], viewport=self.m.viewport)
        n3 = next(iter(t.find(self.w.snap)), None) if self.w.snap is not None else None
        again = value_of(n3) if n3 is not None else None
        steps = done + [what, "reopen the app"] + done
        if again == after:
            return Outcome("proved", "tested", f"changed it ({before} → {after}), reopened the app: still {after}", trace=steps, viewport=self.m.viewport, relevant=1)
        return Outcome(
            "refuted",
            "tested",
            f"changed it ({before} → {after}), reopened the app: {again if again is not None else 'gone'}",
            trace=steps,
            replay={"confirmed": True, "summary": f"{t} was {again} after reopening"},
            viewport=self.m.viewport,
            relevant=1,
        )


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
    """One verdict over every viewport: refuted anywhere is refuted; proved
    needs no open viewport and at least one that was not vacuous."""
    for st in ("refuted", "open"):
        hit = [o for o in outs if o.status == st]
        if hit:
            o = hit[0]
            return Outcome(st, o.method, f"at {o.viewport}: {o.detail}" if len(outs) > 1 else o.detail, o.viewport, o.trace, o.replay, o.relevant)
    real = [o for o in outs if o.status == "proved"]
    status = "proved" if real else "vacuous"
    first = (real or outs)[0]
    return Outcome(status, first.method, _per_viewport(outs), "", first.trace, first.replay, sum(o.relevant for o in real))


def _per_viewport(outs: list[Outcome]) -> str:
    """'x (at 390x844, 1280x800)' when every viewport says the same, else each in turn."""
    if len(outs) == 1:
        return outs[0].detail
    if len({o.detail for o in outs}) == 1:
        return f"{outs[0].detail} (at {', '.join(o.viewport for o in outs)})"
    return "; ".join(f"at {o.viewport}: {o.detail}" for o in outs)
