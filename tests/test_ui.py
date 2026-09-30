"""UI lemmas: the grammar, learning a model from a running app, the verdicts
and what they rest on, and the fixture web app with known-good and known-bad
variants driven through a real browser."""

import json
import shutil
from pathlib import Path

import pytest

from telic.checker import CheckOptions, check
from telic.ui.check import Atoms, ModelCheck, Occlusion, hit_test
from telic.ui.driver import Driver, DriverError
from telic.ui.learn import Explorer, Settings
from telic.ui.spec import Scan, SpecError, parse_prop, scan_source
from telic.ui.tree import Node, Snapshot, actions
from telic.ui.web import parse_aria

APP = Path(__file__).parent / "cases" / "ui" / "app"


# ---------------------------------------------------------------------------
# Grammar


@pytest.mark.parametrize(
    "text, shown",
    [
        ("always reachable home from overlay", "always reachable home from overlay"),
        ('reachable checkbox "Dark mode" is enabled', 'reachable checkbox "Dark mode" is enabled'),
        ('never dialog "Delete" and not button "Cancel"', 'never dialog "Delete" and not button "Cancel"'),
        ('always button "Save" is disabled while textbox "Title" == ""', 'always button "Save" is disabled while textbox "Title" == ""'),
        ('unobscured button "Menu" while screen "/notes/*"', 'unobscured button "Menu" while screen "/notes/*"'),
        ("persists switch /sync/i", "persists switch /(?i)sync/"),
        ('always reachable (screen "/" or screen "/home") from overlay "Settings"', 'always reachable screen "/" or screen "/home" from overlay "Settings"'),
        ('always reachable home from overlay by key "Escape"', 'always reachable home from overlay by key "Escape"'),
        ('always reachable home by tap or button /close/i or key', 'always reachable home by tap or button /(?i)close/ or key'),
    ],
)
def test_properties_parse(text, shown):
    prop, via = parse_prop(text)
    assert str(prop) == shown and via is None


def test_via_names_the_handler():
    prop, via = parse_prop('persists checkbox "Dark mode" via Settings.setDark')
    assert prop.kind == "persists" and via == "Settings.setDark"


@pytest.mark.parametrize(
    "text, says",
    [
        ("eventually home", "expected 'always reachable'"),
        ('reachable button "Save" is shiny', "unknown state 'shiny'"),
        ("unobscured and", "expected a role"),
        ('reachable screen /x/', "quoted path"),
        ('reachable (home', "expected ')'"),
        ("always reachable home by", "expected 'tap', 'key' or a control"),
        ('reachable home by tap', "'by' limits the route of 'always reachable P"),
    ],
)
def test_bad_properties_say_why(text, says):
    with pytest.raises(SpecError, match=says.replace("(", r"\(").replace(")", r"\)")):
        parse_prop(text)


def test_lemmas_are_found_in_any_comment_style():
    src = "\n".join(
        [
            "<!--@ aim ESC: WHILE a dialog is open, the app shall let the user leave it. -->",
            "<script>",
            "  //@ [ESC] ui escape: always reachable home",
            "  //@   from overlay",
            "  //@ [ESC, NAV] ui nav: unobscured link \"Home\"",
            "  //@ ui untagged: reachable home",
            "  //@ [ESC] ui broken: reachable button",
            "</script>",
        ]
    )
    got = Scan()
    scan_source(src, "App.svelte", got)
    assert [(d.id, d.path, d.line) for d in got.aims] == [("ESC", "App.svelte", 1)]
    by = {lem.name: lem for lem in got.lemmas}
    assert str(by["escape"].prop) == "always reachable home from overlay" and by["escape"].aims == ("ESC",)
    assert by["nav"].aims == ("ESC", "NAV") and by["nav"].problem is None
    assert "backs no aim" in by["untagged"].problem
    assert by["broken"].problem is None and str(by["broken"].prop) == "reachable button"


def test_language_frontends_leave_ui_lines_alone(tmp_path):
    (tmp_path / "a.py").write_text('#@ aim ESC: The app shall let the user leave every dialog.\n#@ [ESC] ui escape: always reachable home\n#@   from overlay\n\ndef f(x: int) -> int:\n    #@ ensures result == x\n    return x\n')
    (tmp_path / "b.ts").write_text('//@ [ESC] ui esc2: reachable home\nexport function g(x: number): number {\n  //@ ensures result === x\n  return x;\n}\n')
    rep = check([str(tmp_path / "a.py"), str(tmp_path / "b.ts")], CheckOptions(cache_path=None, lean=False, ui=False), root=str(tmp_path))
    assert not [p for m in rep.modules for p in m.problems]
    assert {f.fn.name: f.status for f in rep.functions} == {"f": "proved", "g": "proved"}
    assert {r.lemma.name for r in rep.ui.results} == {"escape", "esc2"}


# ---------------------------------------------------------------------------
# The accessibility tree


def test_aria_snapshot_parses_roles_names_states_and_refs():
    root = parse_aria(
        "\n".join(
            [
                "- generic [ref=e1]:",
                '  - button "Menu" [expanded] [ref=e2]',
                '  - checkbox "Dark mode" [checked] [ref=e3]',
                '  - textbox "Title" [ref=e4]: abc',
                '  - link "Docs" [ref=e5] [cursor=pointer]:',
                "    - /url: https://example.com",
                "  - generic [ref=e6] [cursor=pointer]: Open card",
                '  - dialog "Help" [ref=e7]:',
                '    - button "Got it" [disabled] [ref=e8]',
            ]
        )
    )
    by = {n.name or n.text(): n for n in root.walk() if n.ref}
    assert by["Menu"].states == {"expanded"} and by["Dark mode"].states == {"checked"}
    assert by["Title"].value == "abc" and by["Docs"].url == "https://example.com"
    assert by["Open card"].pointer and by["Got it"].states == {"disabled"}


def test_repeated_items_are_acted_on_once():
    items = [Node("listitem", children=[Node("button", f"Open {i}", ref=f"o{i}"), Node("button", "Delete", ref=f"d{i}")]) for i in range(3)]
    snap = Snapshot("/", Node("root", children=[Node("list", "Notes", children=items), Node("button", "Add", ref="a")]))
    acts, groups = actions(snap)
    assert sorted(a.sig for a in acts) == ['button "Add"', 'list "Notes" › listitem › button 1', 'list "Notes" › listitem › button 2']
    assert groups == {'list "Notes" › listitem': 3}
    assert {a.ref for a in acts} == {"a", "o0", "d0"}


# ---------------------------------------------------------------------------
# Learning and checking, on an app simulated in Python (any platform the
# driver interface describes)


class FakeApp(Driver):
    """``screens``: name -> (overlay or None, {button: next screen}). Buttons
    named in ``covered`` cannot be clicked; ``hidden`` counts clicks the
    screen does not show (a list that grows)."""

    def __init__(self, screens, start="home", covered=(), menu_covered=()):
        self.screens, self.start, self.covered, self.menu_covered = screens, start, set(covered), set(menu_covered)
        self.at = start
        self.resets = 0

    def reset(self):
        self.at = self.start
        self.resets += 1

    def reopen(self):
        self.at = self.start

    def observe(self):
        overlay, buttons = self.screens[self.at]
        kids = [Node("button", b, ref=b) for b in buttons if not b.startswith("key ")] + [Node("button", "Menu", ref="Menu")]
        root = Node("root", children=kids)
        if overlay:
            root.children.append(Node("dialog", overlay))
        return Snapshot("/" + self.at.split(":")[0], root)

    def do(self, a):
        if a.kind == "key":
            self.at = self.screens[self.at][1].get(a.sig, self.at)
            return
        if a.sig.split('"')[1] in self.covered:
            raise DriverError("covered by div.backdrop")
        nxt = self.screens[self.at][1].get(a.sig.split('"')[1])
        if nxt is not None:
            self.at = nxt

    def uncovered(self, node):
        return True, [("center (1, 1)", "div.toast" if self.at in self.menu_covered else None)]


SCREENS = {
    "home": (None, {"Settings": "home:settings", "About": "about"}),
    "home:settings": ("Settings", {"Close": "home"}),
    "about": (None, {"Back": "home", "Help": "about:help"}),
    "about:help": ("Help", {"Got it": "about"}),
}


def learn(app, lemmas, **kw):
    s = Scan()
    scan_source("\n".join(f"//@ [X] ui {n}: {p}" for n, p in lemmas), "app.js", s)
    atoms = Atoms(s.lemmas)
    occl = {lem.name: Occlusion() for lem in s.lemmas if lem.prop.kind == "unobscured"}

    def probe(state, snap, d, paths):
        for lem in s.lemmas:
            if lem.prop.kind == "unobscured" and lem.prop.cond.eval(snap, ex.model.home):
                occl[lem.name].record(state.id, *hit_test(d, lem.prop.goal, snap), paths)

    ex = Explorer([app], atoms.preds, Settings(**{"keys": (), "workers": 1, **kw}), "fake", probe)
    model = ex.learn()
    mc = ModelCheck(ex, atoms, occl)
    return model, {lem.name: mc.check(lem) for lem in s.lemmas}


def test_every_overlay_can_be_left():
    model, got = learn(FakeApp(SCREENS), [("esc", "always reachable home from overlay"), ("about", 'reachable screen "/about"')])
    assert model.complete and len(model.states) == 4
    assert got["esc"].status == "proved" and "into 2/2 states" in got["esc"].detail
    assert got["about"].status == "proved" and got["about"].trace == ['click button "About"']


def test_a_trap_is_refuted_with_a_replayed_trace():
    screens = dict(SCREENS, **{"about:help": ("Help", {})})
    _, got = learn(FakeApp(screens), [("esc", "always reachable home from overlay")])
    o = got["esc"]
    assert o.status == "refuted" and o.replay["confirmed"]
    assert o.trace == ['click button "About"', 'click button "Help"']
    assert 'dialog "Help"' in o.detail


def test_a_covered_close_button_is_no_way_out():
    _, got = learn(FakeApp(SCREENS, covered={"Got it"}), [("esc", "always reachable home from overlay")])
    assert got["esc"].status == "refuted" and "covered by div.backdrop" in got["esc"].detail


def test_nothing_relevant_is_vacuous_not_proved():
    screens = {"home": (None, {"About": "about"}), "about": (None, {"Back": "home"})}
    _, got = learn(FakeApp(screens), [("esc", "always reachable home from overlay"), ("n", 'never button "Back" while overlay'), ("u", 'unobscured button "Save"')])
    assert {k: o.status for k, o in got.items()} == {"esc": "vacuous", "n": "vacuous", "u": "vacuous"}


def test_invariants_and_occlusion():
    _, got = learn(
        FakeApp(SCREENS, menu_covered={"about"}),
        [("no-close", 'never button "Close" while not overlay'), ("help-only-on-about", 'always screen "/about" while overlay "Help"'), ("menu", 'unobscured button "Menu"')],
    )
    assert got["no-close"].status == "proved" and got["help-only-on-about"].status == "proved"
    m = got["menu"]
    assert m.status == "refuted" and "covered in 1/4 states" in m.detail and m.trace == ['click button "About"']


@pytest.mark.parametrize("walks", [0, 10])
def test_a_dialog_that_traps_only_when_opened_one_way_is_not_proved(walks):
    screens = {
        "home": (None, {"Left": "home:info", "Right": "home:info:trap"}),
        "home:info": ("Info", {"Close": "home"}),
        "home:info:trap": ("Info", {"Close": "home:info:trap"}),
    }
    _, got = learn(FakeApp(screens), [("esc", "always reachable home from overlay")], walks=walks)
    assert got["esc"].status == "open"


@pytest.mark.parametrize("walks", [0, 10])
def test_occlusion_is_tested_at_every_visit_not_once_per_state(walks):
    screens = dict(SCREENS, home=(None, {"Settings": "home:settings", "About": "about", "Other": "about:2"}), **{"about:2": SCREENS["about"]})
    _, got = learn(FakeApp(screens, menu_covered={"about:2"}), [("menu", 'unobscured button "Menu"')], walks=walks)
    m = got["menu"]
    assert m.status == "refuted" and m.replay["confirmed"] and m.trace == ['click button "Other"']


class LateTip(FakeApp):
    """Home offers "Tip" only once the app has been opened a few times."""

    def observe(self):
        snap = super().observe()
        if self.at == "home" and self.resets > 3:
            snap.root.children.append(Node("button", "Tip", ref="Tip"))
        return snap

    def do(self, a):
        if a.sig == 'button "Tip"':
            self.at = "home:tip"
            return
        super().do(a)


def test_an_action_a_later_visit_offers_is_explored_too():
    screens = dict(SCREENS, **{"home:tip": ("Tip", {"Close": "home"})})
    model, got = learn(LateTip(screens), [("esc", "always reachable home from overlay"), ("tip", 'reachable overlay "Tip"')])
    assert model.complete, model.stop
    assert got["esc"].status == "proved" and got["tip"].status == "proved"


def test_budgets_make_the_model_incomplete_and_verdicts_open():
    chain = {f"s{i}": (None, {"Next": f"s{i + 1}"}) for i in range(30)}
    chain["s30"] = ("Trap", {})
    lemmas = [("esc", "always reachable home from overlay"), ("n", "never overlay"), ("t", 'always not overlay while overlay "Trap"'), ("u", 'unobscured button "Menu" while overlay')]
    model, got = learn(FakeApp(chain, start="s0"), lemmas, max_states=10)
    assert not model.complete and "state budget" in model.stop
    # the trap is past the budget: nothing found is not nothing there
    assert {k: o.status for k, o in got.items()} == {"esc": "open", "n": "open", "t": "open", "u": "open"}


class JitteryApp(FakeApp):
    """A FakeApp whose actions take a random while, as a loaded browser's do."""

    def __init__(self, screens, rng, **kw):
        super().__init__(screens, **kw)
        self.rng = rng

    def do(self, a):
        import time

        time.sleep(self.rng.random() / 200)
        super().do(a)


@pytest.mark.parametrize("budget", [100, 12])
def test_the_model_does_not_depend_on_which_browser_is_quicker(budget):
    import random

    grid = {f"{r}{c}": (None, {"Right": f"{r}{min(c + 1, 3)}", "Down": f"{min(r + 1, 3)}{c}", "Home": "00"}) for r in range(4) for c in range(4)}

    def run(jitter):
        rng = random.Random(jitter)
        apps = [JitteryApp(grid, rng, start="00") for _ in range(3)]
        m = Explorer(apps, [], Settings(keys=(), workers=3, max_states=budget, walks=6), "fake").learn()
        return {k: v for k, v in m.dump().items() if k != "seconds"}

    first = run(1)
    assert len(first["states"]) == 16 if budget > 16 else "state budget" in first["stop"]
    assert all(run(j) == first for j in (2, 3))


@pytest.mark.parametrize(
    "ways_out, by, status",
    [
        ({"Close": "home", "key Escape": "home"}, 'key "Escape"', "proved"),
        ({"Close": "home"}, 'key "Escape"', "refuted"),  # Escape does nothing: only the button closes it
        ({"Close": "home"}, "tap", "proved"),
        ({"key Escape": "home"}, "tap", "refuted"),  # only a keyboard gets out: a phone cannot
        ({"key Escape": "home"}, 'key "Escape"', "proved"),
        ({"Close": "home"}, 'button "Close" or key "Escape"', "proved"),
        ({"Close": "home"}, 'button "Cancel"', "refuted"),
    ],
)
def test_an_escape_route_can_be_limited_to_some_actions(ways_out, by, status):
    screens = {"home": (None, {"Open": "home:d"}), "home:d": ("Details", ways_out)}
    _, got = learn(FakeApp(screens), [("esc", f"always reachable home from overlay by {by}")], keys=("Escape",))
    assert got["esc"].status == status
    if status == "refuted":
        assert got["esc"].trace == ['click button "Open"'] and 'dialog "Details"' in got["esc"].detail


def test_actions_a_walk_reveals_are_explored_before_the_model_is_complete():
    # one screen whose "Clear" button only shows after two adds: only a walk gets there
    screens = {"home:0": (None, {"Add": "home:1"}), "home:1": (None, {"Add": "home:2"}), "home:2": (None, {"Add": "home:2", "Clear": "home:0"})}
    model, _ = learn(FakeApp(screens, start="home:0"), [("r", "reachable home")], abstraction="screens", walks=10)
    assert 'button "Clear"' in model.states[0].actions
    assert model.complete and 'button "Clear"' in model.states[0].fired


def test_the_screens_pass_gets_the_whole_time_budget():
    from types import SimpleNamespace

    from telic.ui.run import learn_auto

    passes = []

    def learn(s):
        passes.append(s)
        return None, SimpleNamespace(stop="stopped at the state budget (100)" if s.abstraction == "controls" else "", seconds=590.0, notes=[]), {}

    learn_auto(learn, Settings(max_seconds=600.0))
    assert [(p.abstraction, p.max_seconds) for p in passes] == [("controls", 600.0), ("screens", 600.0)]


# ---------------------------------------------------------------------------
# The fixture web app in a real browser


def _browser():
    try:
        from playwright.sync_api import sync_playwright

        with sync_playwright() as p:
            p.chromium.launch().close()
        return True
    except Exception:  # noqa: BLE001 - not installed
        return False


needs_browser = pytest.mark.skipif(not _browser(), reason="Playwright with Chromium not available")


def fixture_app(tmp_path, bugs=(), viewports=("1280x800",)):
    d = tmp_path / "app"
    shutil.copytree(APP, d)
    (d / "bugs.js").write_text(f"window.BUGS = {json.dumps(list(bugs))};\n")
    toml = (d / "telic.toml").read_text().replace('viewports = ["390x844", "1280x800"]', f"viewports = {json.dumps(list(viewports))}")
    (d / "telic.toml").write_text(toml + "walks = 4\n")
    return d


def run_ui(d):
    rep = check([str(d)], CheckOptions(cache_path=None, lean=False), root=str(d))
    return rep, {r.lemma.name: r for r in rep.ui.results}


@needs_browser
def test_fixture_app_keeps_every_promise(tmp_path):
    d = fixture_app(tmp_path)
    rep, got = run_ui(d)
    assert {k: r.status for k, r in got.items()} == {"escape": "proved", "dark-mode-shown": "proved", "dark-mode": "proved", "menu-visible": "proved"}
    assert {i.id: i.status for i in rep.aims} == {"ESCAPE": "backed", "SETTINGS": "backed", "NAV": "backed"}
    (m,) = rep.ui.apps[0].models
    assert m["complete"] and m["states"] > 5
    # Nothing the app is built from changed: the verdicts come from the cache.
    rep, again = run_ui(d)
    assert all(r.cached for r in again.values()) and rep.ui.apps[0].cached
    (d / "app.js").write_text((d / "app.js").read_text() + "\n// touched\n")
    _, third = run_ui(d)
    assert not any(r.cached for r in third.values())


@pytest.mark.parametrize(
    "bug, lemma, says",
    [
        ("trap", "escape", 'stuck at screen / with dialog "Help" open'),
        ("forget", "dark-mode", "reopened the app: unchecked"),
    ],
)
@needs_browser
def test_fixture_bugs_are_found_and_replayed(tmp_path, bug, lemma, says):
    d = fixture_app(tmp_path, [bug])
    rep, got = run_ui(d)
    r = got[lemma]
    assert r.status == "refuted" and says in r.detail and r.replay["confirmed"] and r.trace
    assert {k for k, x in got.items() if x.status == "refuted"} == {lemma}
    assert not rep.ok


@needs_browser
def test_a_banner_that_covers_the_menu_on_phones_only(tmp_path):
    d = fixture_app(tmp_path, ["banner"], viewports=("390x844", "1280x800"))
    _, got = run_ui(d)
    r = got["menu-visible"]
    assert r.status == "refuted" and "at 390x844" in r.detail and 'div.banner "We use cookies"' in r.detail
    assert [v["status"] for v in r.viewports] == ["refuted", "proved"]


@pytest.mark.parametrize(
    "toml, says",
    [
        ('command = "exit 3"', "exited (3)"),
        ('static = "missing"', "does not exist"),
        ('url = "http://127.0.0.1:9"', "nothing answers"),
    ],
)
def test_an_app_that_does_not_run_is_an_error_not_a_verdict(tmp_path, toml, says):
    d = tmp_path / "app"
    shutil.copytree(APP, d)
    (d / "telic.toml").write_text(f'[ui]\n{toml}\nviewports = ["390x844"]\n')
    rep, got = run_ui(d)
    assert {r.status for r in got.values()} == {"error"}
    assert all(says in r.detail for r in got.values())
    assert {a.status for a in rep.aims} == {"partial"}


@pytest.mark.parametrize("viewports, ok", [('["390x844"]', True), ("[]", False)])
def test_viewports_must_name_at_least_one(tmp_path, viewports, ok):
    from telic.ui.config import ConfigError, load

    (tmp_path / "telic.toml").write_text(f'[ui]\nurl = "http://localhost:1"\nviewports = {viewports}\n')
    if ok:
        assert load(str(tmp_path / "telic.toml"), str(tmp_path)).viewports == [(390, 844)]
    else:
        with pytest.raises(ConfigError, match="viewports is empty"):
            load(str(tmp_path / "telic.toml"), str(tmp_path))


def test_a_form_is_filled_in_and_sent_as_one_action():
    form = [Node("textbox", "Email", ref="e", form="Sign in"), Node("textbox", "Password", ref="p", form="Sign in"), Node("button", "Sign in", ref="b")]
    snap = Snapshot("/login", Node("root", children=form + [Node("searchbox", "Search", ref="s")]))
    acts = {a.sig: a for a in actions(snap, fill=(("Search", "milk"),))[0]}
    assert sorted(acts) == ['button "Sign in"', 'fill searchbox "Search"', 'submit form "Sign in"']
    sent = acts['submit form "Sign in"']
    assert sent.ref == "b" and json.loads(sent.arg) == [["e", "telic@example.com"], ["p", "Telic-pass-123"]]
    assert acts['fill searchbox "Search"'].arg == "milk"


def test_counts_in_names_are_data():
    one = Snapshot("/", Node("root", children=[Node("link", "All tasks 5", ref="a")]))
    two = Snapshot("/", Node("root", children=[Node("link", "All tasks 6", ref="a")]))
    assert [a.sig for a in actions(one)[0]] == [a.sig for a in actions(two)[0]] == ['link "All tasks #"']


def test_screens_abstraction_keeps_only_what_the_lemmas_see():
    # a wizard on one screen the lemmas do not look into: each step shows other controls
    steps = "ABCDEFGHIJ"
    screens = {f"home:{c}": (None, {f"Step {c}": f"home:{steps[min(i + 1, 9)]}"}) for i, c in enumerate(steps)}
    fine, _ = learn(FakeApp(screens, start="home:A"), [("r", "reachable home")])
    coarse, got = learn(FakeApp(screens, start="home:A"), [("r", "reachable home")], abstraction="screens")
    assert len(fine.states) == 10 and len(coarse.states) == 1 and coarse.complete
    assert got["r"].status == "proved"


# ---------------------------------------------------------------------------
# Sharing the machine: a browser budget across processes, and no orphans

HOLDER = "import sys, time; from telic.ui import slots\nwith slots.hold(1):\n    print('held', flush=True)\n    time.sleep(60)\n"


@pytest.mark.parametrize("ends", ["exits", "is killed"])
def test_a_browser_slot_is_released_however_its_holder_ends(tmp_path, monkeypatch, ends):
    import signal
    import subprocess
    import sys

    from telic.ui import slots

    monkeypatch.setenv("TELIC_UI_SLOTS", "1")
    monkeypatch.setenv("TELIC_SLOTS_DIR", str(tmp_path))
    holder = subprocess.Popen([sys.executable, "-c", HOLDER], stdout=subprocess.PIPE, text=True)
    try:
        assert holder.stdout.readline().strip() == "held"
        with pytest.raises(slots.SlotTimeout):
            with slots.hold(1, timeout=0.5):
                pass
        holder.send_signal(signal.SIGTERM if ends == "exits" else signal.SIGKILL)
        holder.wait(timeout=10)
        with slots.hold(1, timeout=5) as n:
            assert n == 1
    finally:
        holder.kill()


@pytest.mark.parametrize("budget", [1, 2])
@needs_browser
def test_concurrent_browsers_never_exceed_the_machine_budget(tmp_path, monkeypatch, budget):
    import threading

    from telic.ui.web import WebDriver

    monkeypatch.setenv("TELIC_UI_SLOTS", str(budget))
    monkeypatch.setenv("TELIC_SLOTS_DIR", str(tmp_path))
    live, peak, lock = [0], [0], threading.Lock()
    start, stop = WebDriver.start, WebDriver.stop

    def counted_start(self):
        with lock:
            live[0] += 1
            peak[0] = max(peak[0], live[0])
        start(self)

    def counted_stop(self):
        stop(self)
        with lock:
            live[0] -= 1

    monkeypatch.setattr(WebDriver, "start", counted_start)
    monkeypatch.setattr(WebDriver, "stop", counted_stop)
    d = fixture_app(tmp_path, viewports=("390x844", "1280x800", "1024x768"))
    _, got = run_ui(d)
    assert got["escape"].status == "proved", got["escape"].detail
    assert peak[0] == budget and live[0] == 0


@pytest.mark.parametrize("sig", ["SIGTERM", "SIGINT", "SIGKILL"])
@needs_browser
def test_nothing_telic_started_outlives_it(tmp_path, sig):
    import os
    import signal
    import subprocess
    import sys
    import time

    d = fixture_app(tmp_path)
    running: set[int] = set()
    toml = (d / "telic.toml").read_text().replace('static = "."', f'command = "{sys.executable} -m http.server {{port}} --bind 127.0.0.1"')
    (d / "telic.toml").write_text(toml + "max_seconds = 300\n")
    # its own browser budget: another telic run on the machine may hold the shared slots
    env = dict(os.environ, PYTHONPATH=str(Path(__file__).resolve().parents[1]), TELIC_SLOTS_DIR=str(tmp_path / "slots"))
    proc = subprocess.Popen([sys.executable, "-m", "telic.cli", "check", str(d), "--no-cache"], cwd=d, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def tree() -> set[int]:
        rows = [ln.split() for ln in subprocess.run(["ps", "-A", "-o", "pid=,ppid=,command="], capture_output=True, text=True).stdout.splitlines()]
        kids: dict[int, list[int]] = {}
        for r in rows:
            kids.setdefault(int(r[1]), []).append(int(r[0]))
        out, todo = set(), [proc.pid]
        while todo:
            p = todo.pop()
            out.add(p)
            todo += kids.get(p, [])
        return out - {proc.pid}

    def commands(pids: set[int]) -> list[str]:
        got = subprocess.run(["ps", "-o", "command=", "-p", ",".join(map(str, pids))], capture_output=True, text=True).stdout if pids else ""
        return got.splitlines()

    try:
        deadline = time.monotonic() + 60
        while time.monotonic() < deadline:
            running = tree()
            names = " ".join(commands(running))
            if "http.server" in names and "headless" in names:
                break
            time.sleep(0.3)
        else:
            pytest.fail("the app and a browser never started")
        proc.send_signal(getattr(signal, sig))
        proc.wait(timeout=30)
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline and commands(running):
            time.sleep(0.3)
        assert commands(running) == []
    finally:
        proc.kill()
        for pid in running:
            try:
                os.kill(pid, signal.SIGKILL)
            except OSError:
                pass


# ---------------------------------------------------------------------------
# What the verdict cache is keyed by


@pytest.mark.parametrize(
    "path, counts",
    [("src/App.tsx", True), ("src/build/Button.tsx", True), (".env", True), ("dist/app.js", False), ("node_modules/x/index.js", False)],
)
def test_the_cache_key_follows_what_the_app_is_built_from(tmp_path, path, counts):
    from telic.ui.app import build_digest
    from telic.ui.config import load

    (tmp_path / "telic.toml").write_text('[ui]\ncommand = "npx vite --port {port}"\n')
    f = tmp_path / path
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text("one")
    cfg = load(str(tmp_path / "telic.toml"), str(tmp_path))
    before = build_digest(cfg)
    f.write_text("two")
    assert (build_digest(cfg) != before) == counts


def test_an_app_telic_does_not_start_is_keyed_by_what_it_serves(tmp_path):
    import functools
    import http.server
    import threading

    from telic.ui.app import build_digest
    from telic.ui.config import load

    site = tmp_path / "site"
    site.mkdir()
    (site / "index.html").write_text('<script src="/app-1.js"></script>')
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), functools.partial(http.server.SimpleHTTPRequestHandler, directory=str(site)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    try:
        app = tmp_path / "app"
        app.mkdir()
        (app / "telic.toml").write_text(f'[ui]\nurl = "http://127.0.0.1:{server.server_address[1]}/"\n')
        cfg = load(str(app / "telic.toml"), str(tmp_path))
        before = build_digest(cfg)
        assert build_digest(cfg) == before
        (site / "index.html").write_text('<script src="/app-2.js"></script>')
        assert build_digest(cfg) != before
    finally:
        server.shutdown()
        server.server_close()


# ---------------------------------------------------------------------------
# What a person sees and can reach, in a real browser

TINY = "<!doctype html><html lang=en><head><meta charset=utf-8><style>body{{margin:0}} {css}</style></head><body><main>{body}</main><script src=app.js></script></body></html>"


def tiny_app(tmp_path, lemma, body, js="", css=""):
    d = tmp_path / "tiny"
    d.mkdir()
    (d / "telic.toml").write_text('[ui]\nstatic = "."\nviewports = ["1280x800"]\nwalks = 2\n')
    (d / "index.html").write_text(TINY.format(body=body, css=css))
    (d / "app.js").write_text(f"//@ aim A: The app shall work.\n//@   by: x\n//@ [A] ui x: {lemma}\n{js}\n")
    return d


MENU = '<button id=menu onclick="">Menu</button>'


@pytest.mark.parametrize(
    "lemma, body, js, css, status, says",
    [
        ('unobscured button "Save"', '<div style="height:80px;overflow:hidden"><div style="height:600px"></div><button>Save</button></div>', "", "", "refuted", "covered by"),
        ('unobscured button "Save"', '<div style="height:80px;overflow:auto"><div style="height:600px"></div><button>Save</button></div>', "", "", "proved", ""),
        ('unobscured button "Menu"', MENU + "<div class=veil>Sale</div>", "", ".veil{position:fixed;top:0;left:0;width:300px;height:90px;background:#c00;pointer-events:none}", "refuted", "painted over it"),
        ('unobscured button "Menu"', MENU + "<div class=veil></div>", "", ".veil{position:fixed;inset:0;pointer-events:none}", "proved", ""),
        ('unobscured button "Menu"', MENU + '<div role=dialog aria-label="Cookies" class=ban>We use cookies</div>', "", ".ban{position:fixed;top:0;left:0;right:0;height:60px;background:#fd0}", "refuted", "Cookies"),
        ('unobscured button "Menu" while not overlay', MENU + '<div class=bd><div role=dialog aria-modal=true aria-label="Hi">Hi</div></div>', "", ".bd{position:fixed;inset:0;background:#0006}", "vacuous", ""),
        # a dialog titled by its heading is named as a screen reader names it (two such dialogs are not one state)
        ('reachable overlay "Delete item?"', '<button onclick="document.querySelector(\'main\').insertAdjacentHTML(\'beforeend\', \'<div role=dialog aria-labelledby=t><h2 id=t>Delete item?</h2></div>\')">Delete</button>', "", "", "proved", "reached in 1 step"),
        ('never overlay "Expired"', "<p>Hi</p>", "setTimeout(() => document.querySelector('main').insertAdjacentHTML('beforeend', '<div role=dialog aria-label=Expired>Expired</div>'), 1500);", "", "refuted", "Expired"),
    ],
)
@needs_browser
def test_what_a_person_sees_and_can_reach(tmp_path, lemma, body, js, css, status, says):
    _, got = run_ui(tiny_app(tmp_path, lemma, body, js, css))
    assert (got["x"].status, says in got["x"].detail) == (status, True), got["x"].detail
