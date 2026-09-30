"""Learning the app's state graph from the running app.

Nothing is read from source. From a fresh start, every action a user has
(clicking, typing, choosing, pressing a key) is fired in every state found,
each observation is abstracted to what the lemmas can tell apart (screen,
open overlays, controls and their states, the predicates the lemmas use),
and the transitions form the model. Getting back to a state replays its
access sequence from a fresh start, as in active automata learning.

The model is then conformance-tested: random walks through it are replayed
in the app step by step, and every step whose outcome the model did not
predict is added to it (the app is the judge), after which learning resumes.
A model proposed by an oracle from reading the source can seed the search;
its predictions are tested the same way and never trusted.
"""

from __future__ import annotations

import hashlib
import json
import random
import threading
import time
from collections import deque
from dataclasses import dataclass, field
from typing import Callable

from .driver import Driver, DriverError
from .spec import Pred
from .tree import LANDMARKS, Action, Snapshot, actions, bucket, controls

RESET_COST = 3  # a fresh start costs about as much as this many actions


@dataclass
class Settings:
    max_states: int = 300
    max_depth: int = 30
    max_seconds: float = 600.0
    walks: int = 10
    walk_length: int = 0  # 0: two more than the deepest state
    workers: int = 1  # browsers per viewport: more only when asked for
    text: str = "telic"
    fill: tuple[tuple[str, str], ...] = ()  # (name regex, value) tried before the built-in guesses
    # "controls": a state is the screen, overlays, controls and lists; "screens": only
    # the screen, overlays, open menus and the lemmas' predicates (smaller, less exact)
    abstraction: str = "auto"  # auto: controls, or screens when controls exceed a budget
    keys: tuple[str, ...] = ("Escape",)
    ignore: tuple[str, ...] = ()
    seed: int = 0


@dataclass
class UiState:
    id: int
    key: str
    screen: str
    overlays: list[str]
    atoms: tuple[bool, ...]
    actions: list[str]
    labels: dict[str, str]
    access: list[str]
    depth: int
    fired: set[str] = field(default_factory=set)
    blocked: dict[str, str] = field(default_factory=dict)
    body: dict = field(default_factory=dict)  # what the key is a hash of
    history: list[str] = field(default_factory=list)  # the actions that first led here

    def describe(self) -> str:
        s = f"screen {self.screen}"
        if self.overlays:
            s += " with " + ", ".join(self.overlays) + " open"
        return s


@dataclass
class Model:
    viewport: str
    abstraction: str = "controls"
    home: str = "/"
    states: list[UiState] = field(default_factory=list)
    trans: dict[int, dict[str, set[int]]] = field(default_factory=dict)
    complete: bool = False
    stop: str = ""
    fired: int = 0
    resets: int = 0
    seconds: float = 0.0
    walks: int = 0
    walk_length: int = 0
    agreed: int = 0
    disagreed: list[str] = field(default_factory=list)
    seeded: dict[str, int] = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)
    unreproducible: set[int] = field(default_factory=set)  # seen once, never reached again by any known path

    @property
    def transitions(self) -> int:
        return sum(len(ts) for m in self.trans.values() for ts in m.values())

    @property
    def nondeterministic(self) -> int:
        return sum(1 for m in self.trans.values() for ts in m.values() if len(ts) > 1)

    def edges(self, sid: int):
        for sig, ts in self.trans.get(sid, {}).items():
            for t in ts:
                yield sig, t

    def path(self, frm: int, goals: set[int], deterministic: bool = False, avoid: set[tuple[int, str]] = frozenset()) -> list[str] | None:
        """Shortest action sequence from ``frm`` to any of ``goals``."""
        if frm in goals:
            return []
        prev: dict[int, tuple[int, str]] = {frm: (-1, "")}
        q = deque([frm])
        while q:
            s = q.popleft()
            for sig, ts in self.trans.get(s, {}).items():
                if (deterministic and len(ts) > 1) or (s, sig) in avoid:
                    continue
                for t in ts:
                    if t in prev:
                        continue
                    prev[t] = (s, sig)
                    if t in goals:
                        out = []
                        while t != frm:
                            t, sig2 = prev[t]
                            out.append(sig2)
                        return out[::-1]
                    q.append(t)
        return None

    def reaching(self, goals: set[int]) -> set[int]:
        """States from which some path reaches ``goals``."""
        back: dict[int, set[int]] = {}
        for s, m in self.trans.items():
            for ts in m.values():
                for t in ts:
                    back.setdefault(t, set()).add(s)
        out = set(goals)
        q = deque(goals)
        while q:
            t = q.popleft()
            for s in back.get(t, ()):
                if s not in out:
                    out.add(s)
                    q.append(s)
        return out

    def closed_from(self, sid: int) -> bool:
        """Every state reachable from ``sid`` has had every action fired."""
        seen = {sid}
        q = deque([sid])
        while q:
            s = self.states[q.popleft()]
            if any(a not in s.fired for a in s.actions):
                return False
            for _, t in self.edges(s.id):
                if t not in seen:
                    seen.add(t)
                    q.append(t)
        return True

    def labels(self, sigs: list[str]) -> list[str]:
        """What a person reads for an access path (labels as first seen)."""
        out, s = [], self.states[0] if self.states else None
        for sig in sigs:
            out.append(s.labels.get(sig, sig) if s else sig)
            nxt = sorted(self.trans.get(s.id, {}).get(sig, ())) if s else []
            s = self.states[nxt[0]] if nxt else None
        return out

    def dump(self) -> dict:
        """The whole model, for reading or diffing: states and transitions."""
        return {
            **self.summary(),
            "home": self.home,
            "states": [
                {"id": s.id, "describe": s.describe(), "access": self.labels(s.access), "depth": s.depth, "state": s.body, "blocked": s.blocked, "untried": [a for a in s.actions if a not in s.fired], **({"unreproducible": True} if s.id in self.unreproducible else {})}
                for s in self.states
            ],
            "transitions": [{"from": s, "action": sig, "to": sorted(ts)} for s, m in sorted(self.trans.items()) for sig, ts in sorted(m.items())],
        }

    def summary(self) -> dict:
        return {
            "viewport": self.viewport,
            "abstraction": self.abstraction,
            "states": len(self.states),
            "transitions": self.transitions,
            "complete": self.complete,
            "stop": self.stop,
            "fired": self.fired,
            "resets": self.resets,
            "seconds": round(self.seconds, 1),
            "walks": self.walks,
            "walk_length": self.walk_length,
            "agreed": self.agreed,
            "disagreed": self.disagreed[:10],
            "nondeterministic": self.nondeterministic,
            "seeded": self.seeded,
            "unreproducible": len(self.unreproducible),
            "notes": self.notes,
        }


class Worker:
    """One browser (or device) driving the app, and where it is now."""

    def __init__(self, driver: Driver):
        self.d = driver
        self.cur: UiState | None = None
        self.snap: Snapshot | None = None
        self.acts: dict[str, Action] = {}
        self.history: list[str] = []  # everything done since the last fresh start


class Explorer:
    """Learns one model with several workers side by side: each claims an
    untried action of some state, gets there and fires it."""

    def __init__(
        self,
        drivers: list[Driver],
        atoms: list[Pred],
        settings: Settings,
        viewport: str,
        probe: Callable[[UiState, Snapshot, Driver], None] | None = None,
        log: Callable[[str], None] | None = None,
    ):
        self.workers = [Worker(d) for d in drivers]
        self.atoms = atoms
        self.s = settings
        self.model = Model(viewport, "screens" if settings.abstraction == "screens" else "controls")
        self.probe = probe
        self.log = log or (lambda _m: None)
        self.by_key: dict[str, UiState] = {}
        self.lock = threading.RLock()
        self.claimed: set[tuple[int, str]] = set()
        self.t0 = time.monotonic()

    @property
    def main(self) -> Worker:
        return self.workers[0]

    # -- observation ---------------------------------------------------------

    def known(self, snap: Snapshot, d: Driver) -> UiState | None:
        """The model's state for this observation, if it has one."""
        with self.lock:
            return self.by_key.get(self._abstract(snap, d)[0])

    def _abstract(self, snap: Snapshot, d: Driver) -> tuple[str, tuple[bool, ...], dict]:
        acts, groups = actions(snap, text=self.s.text, fill=self.s.fill, keys=(), ignore=self.s.ignore, leaves=d.leaves)
        home = self.model.home if self.model.states else snap.screen
        atoms = tuple(p.eval(snap, home) for p in self.atoms)
        if self.s.abstraction == "screens":
            body = {
                "screen": snap.screen,
                "overlays": snap.overlays(),
                "open": [c for c in controls(snap) if "[expanded]" in c or "[pressed]" in c],
                "landmarks": sorted({n.label for n in snap.nodes() if n.role in LANDMARKS and n.name}),
                "atoms": list(atoms),
            }
        else:
            body = {
                "screen": snap.screen,
                "overlays": snap.overlays(),
                "actions": sorted({a.sig for a in acts}),
                "controls": controls(snap),
                "groups": {g: bucket(n) for g, n in sorted(groups.items())},
                "atoms": list(atoms),
            }
        return hashlib.sha256(json.dumps(body, sort_keys=True, ensure_ascii=False).encode()).hexdigest()[:20], atoms, body

    def look(self, w: Worker) -> Snapshot:
        snap = w.d.observe()
        acts, _ = actions(snap, text=self.s.text, fill=self.s.fill, keys=self.s.keys, ignore=self.s.ignore, leaves=w.d.leaves)
        w.snap = snap
        w.acts = {}
        for a in acts:
            w.acts.setdefault(a.sig, a)
        return snap

    def _intern(self, w: Worker, snap: Snapshot, parent: UiState | None, sig: str | None) -> UiState:
        new = False
        with self.lock:
            key, atoms, body = self._abstract(snap, w.d)
            st = self.by_key.get(key)
            if st is None:
                access = (parent.access + [sig]) if parent is not None and sig is not None else []
                st = UiState(len(self.model.states), key, snap.screen, snap.overlays(), atoms, list(w.acts), {s: a.label for s, a in w.acts.items()}, access, len(access), body=body)
                # what this worker actually did to get here: the short path can pass
                # through states that only look the same, so it is the fallback
                st.history = list(w.history) if parent is not None else []
                self.model.states.append(st)
                self.model.trans[st.id] = {}
                self.by_key[key] = st
                if st.id == 0:
                    self.model.home = snap.screen
                new = True
            else:
                for sig2, a in w.acts.items():  # a coarse state offers what any visit to it offered
                    if sig2 not in st.labels:
                        st.actions.append(sig2)
                        st.labels[sig2] = a.label
        if new and self.probe is not None:
            self.probe(st, snap, w.d)
        return st

    # -- moving ----------------------------------------------------------------

    def reset(self, w: Worker) -> UiState:
        w.d.reset()
        w.history = []
        snap = self.look(w)
        st = self._intern(w, snap, None, None)
        with self.lock:
            self.model.resets += 1
            note = "a fresh start does not always show the same first screen"
            if st.id != 0 and note not in self.model.notes:
                self.model.notes.append(note)
        w.cur = st
        return st

    def fire(self, w: Worker, s: UiState, sig: str) -> UiState | None:
        """Fire ``sig`` where ``w`` is (which must be ``s``)."""
        a = w.acts.get(sig)
        with self.lock:
            s.fired.add(sig)
        if a is None:
            with self.lock:
                s.blocked.setdefault(sig, "not offered in this state now")
            w.cur = None
            return None
        with self.lock:
            self.model.fired += 1
        try:
            w.d.do(a)
        except DriverError as e:
            with self.lock:
                s.blocked[sig] = str(e)
            if e.moved:
                w.cur = None
            return None
        w.history.append(sig)
        snap = self.look(w)
        t = self._intern(w, snap, s, sig)
        with self.lock:
            self.model.trans[s.id].setdefault(sig, set()).add(t.id)
            s.blocked.pop(sig, None)
        w.cur = t
        return t

    def follow(self, w: Worker, sigs: list[str]) -> bool:
        for sig in sigs:
            if w.cur is None or sig not in w.acts:
                return False
            if self.fire(w, w.cur, sig) is None:
                return False
        return True

    def goto(self, w: Worker, target: UiState) -> bool:
        if w.cur is target:
            return True
        if w.cur is not None:
            with self.lock:
                p = self.model.path(w.cur.id, {target.id}, deterministic=True)
            if p is not None and len(p) < len(target.access) + RESET_COST:
                if self.follow(w, p) and w.cur is target:
                    return True
        with self.lock:
            # its own path, twice; then the paths of other transitions into it
            tries = [target.access, target.history if target.history != target.access else target.access] + [
                self.model.states[p].access + [sig]
                for p, m in self.model.trans.items()
                for sig, ts in m.items()
                if target.id in ts and self.model.states[p].access + [sig] != target.access
            ][:3]
        for path in tries:
            self.reset(w)
            if self.follow(w, path) and w.cur is target:
                if path is not target.access and len(path) <= len(target.access) + RESET_COST * 3:
                    with self.lock:
                        target.access, target.depth = list(path), len(path)
                return True
        with self.lock:
            self.model.unreproducible.add(target.id)
        return False

    # -- learning --------------------------------------------------------------

    def _over(self) -> str:
        if time.monotonic() - self.t0 > self.s.max_seconds:
            return f"stopped at the time budget ({self.s.max_seconds:.0f}s)"
        if len(self.model.states) >= self.s.max_states:
            return f"stopped at the state budget ({self.s.max_states})"
        return ""

    def _claim(self, w: Worker) -> tuple[UiState, str] | None:
        """A state with an action nobody has tried or claimed: first the
        first-found variant of each screen (route and open overlays), so a
        budget buys breadth; among those, the nearest."""
        def untried(s: UiState) -> str | None:
            return next((a for a in s.actions if a not in s.fired and (s.id, a) not in self.claimed), None)

        rank: dict[int, int] = {}
        seen: dict[tuple, int] = {}
        for x in self.model.states:
            g = (x.screen, tuple(x.overlays))
            rank[x.id] = seen.get(g, 0)
            seen[g] = rank[x.id] + 1
        # where the worker already is costs nothing, and a state no path reaches again can only be explored from there
        c = w.cur
        if c is not None and c.depth < self.s.max_depth and (rank[c.id] == 0 or c.id in self.model.unreproducible):
            sig = untried(c)
            if sig is not None:
                self.claimed.add((c.id, sig))
                return c, sig
        todo = [s for s in self.model.states if s.depth < self.s.max_depth and s.id not in self.model.unreproducible and untried(s) is not None]
        if not todo:
            return None
        dist: dict[int, int] = {}
        if w.cur is not None:
            dist[w.cur.id] = 0
            q = deque([w.cur.id])
            while q:
                x = q.popleft()
                for ts in self.model.trans.get(x, {}).values():
                    if len(ts) == 1:
                        (t,) = ts
                        if t not in dist:
                            dist[t] = dist[x] + 1
                            q.append(t)
        s = min(todo, key=lambda s: (rank[s.id], dist.get(s.id, len(s.access) + RESET_COST), s.depth, s.id))
        sig = next(a for a in s.actions if a not in s.fired and (s.id, a) not in self.claimed)
        self.claimed.add((s.id, sig))
        return s, sig

    def _pool(self, job: Callable[[Worker], None]) -> None:
        if len(self.workers) == 1:
            job(self.workers[0])
            return
        errors: list[BaseException] = []

        def run(w: Worker) -> None:
            try:
                job(w)
            except BaseException as e:  # noqa: BLE001 - re-raised in the caller
                errors.append(e)

        ts = [threading.Thread(target=run, args=(w,), daemon=True) for w in self.workers]
        for t in ts:
            t.start()
        for t in ts:
            t.join()
        if errors:
            raise errors[0]

    def explore(self) -> None:
        busy = [0]

        def work(w: Worker) -> None:
            while True:
                with self.lock:
                    stop = self._over()
                    if stop:
                        self.model.stop = stop
                        return
                    got = self._claim(w)
                    if got is None and busy[0] == 0:
                        return
                    if got is not None:
                        busy[0] += 1
                if got is None:
                    time.sleep(0.02)
                    continue
                s, sig = got
                try:
                    if w.cur is s or (s.id not in self.model.unreproducible and self.goto(w, s)):
                        self.fire(w, s, sig)
                finally:
                    with self.lock:
                        self.claimed.discard((s.id, sig))
                        busy[0] -= 1
                        if self.model.fired % 25 == 0:
                            self.log(f"{len(self.model.states)} states, {self.model.fired} actions")

        self._pool(work)

    def conform(self) -> bool:
        """Random walks through the model, replayed in the app. True if the
        app did something the model did not predict."""
        length = self.s.walk_length or (max(s.depth for s in self.model.states) + 2)
        todo = list(range(self.s.walks))
        surprised = [False]

        def work(w: Worker) -> None:
            while True:
                with self.lock:
                    if not todo or self._over():
                        return
                    n = todo.pop()
                    self.model.walks += 1
                rng = random.Random(self.s.seed * 7919 + n + 1000 * self.model.resets)
                s = self.reset(w)
                for _ in range(length):
                    with self.lock:
                        options = sorted(sig for sig in s.actions if self.model.trans[s.id].get(sig))
                        if not options:
                            break
                        sig = rng.choice(options)
                        predicted = set(self.model.trans[s.id][sig])
                    t = self.fire(w, s, sig)
                    with self.lock:
                        if t is None:
                            self.model.disagreed.append(f"{s.labels.get(sig, sig)} in {s.describe()}: now blocked ({s.blocked.get(sig)})")
                            surprised[0] = True
                        elif t.id not in predicted:
                            self.model.disagreed.append(f"{s.labels.get(sig, sig)} in {s.describe()}: reached {t.describe()}, not what the model predicted")
                            surprised[0] = True
                        else:
                            self.model.agreed += 1
                    if t is None:
                        break
                    s = t

        self._pool(work)
        self.model.walk_length = max(self.model.walk_length, length)
        return surprised[0]

    def seed(self, paths: list[list[str]]) -> None:
        """Replay action sequences an oracle predicted; each step it got
        right or wrong is counted, and what the app did is kept."""
        agreed = wrong = 0
        w = self.main
        for p in paths:
            if self._over():
                break
            s = self.reset(w)
            for want in p:
                sig = next((k for k, a in w.acts.items() if want in (k, a.label) or a.label.endswith(" " + want)), None)
                if sig is None:
                    wrong += 1
                    break
                t = self.fire(w, s, sig)
                if t is None:
                    wrong += 1
                    break
                agreed += 1
                s = t
        self.model.seeded = {"paths": len(paths), "steps_agreed": agreed, "steps_wrong": wrong}

    def learn(self, seeds: list[list[str]] | None = None, rounds: int = 3) -> Model:
        self.reset(self.main)
        if seeds:
            self.seed(seeds)
        for r in range(rounds + 1):
            self.explore()
            if self.model.stop or not self.s.walks or r == rounds or not self.conform():
                break
        pending = sum(1 for s in self.model.states if s.id not in self.model.unreproducible for a in s.actions if a not in s.fired)
        if not self.model.stop and pending:
            self.model.stop = f"stopped at the depth bound ({self.s.max_depth})"
        if not self.model.stop and self.model.unreproducible:
            n = len(self.model.unreproducible)
            self.model.stop = f"{n} state{'s' * (n != 1)} seen once that no known path reaches again (the app is not deterministic there)"
        self.model.complete = not self.model.stop
        self.model.seconds = time.monotonic() - self.t0
        return self.model
