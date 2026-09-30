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
        kids = [Node("button", b, ref=b) for b in buttons] + [Node("button", "Menu", ref="Menu")]
        root = Node("root", children=kids)
        if overlay:
            root.children.append(Node("dialog", overlay))
        return Snapshot("/" + self.at.split(":")[0], root)

    def do(self, a):
        if a.kind == "key":
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

    def probe(state, snap, d):
        for lem in s.lemmas:
            if lem.prop.kind == "unobscured" and lem.prop.cond.eval(snap, ex.model.home):
                n, bad = hit_test(d, lem.prop.goal, snap)
                occl[lem.name].rendered[state.id] = n
                if bad:
                    occl[lem.name].covered[state.id] = bad

    ex = Explorer([app], atoms.preds, Settings(keys=(), workers=1, **kw), "fake", probe)
    model = ex.learn()
    mc = ModelCheck(ex, atoms, occl)
    return model, {lem.name: mc.check(lem) for lem in s.lemmas}


def test_every_overlay_can_be_left():
    model, got = learn(FakeApp(SCREENS), [("esc", "always reachable home from overlay"), ("about", 'reachable screen "/about"')])
    assert model.complete and len(model.states) == 4
    assert got["esc"].status == "proved" and "routes replayed from 2/2" in got["esc"].detail
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


def test_budgets_make_the_model_incomplete_and_verdicts_open():
    chain = {f"s{i}": (None, {"Next": f"s{i + 1}"}) for i in range(30)}
    chain["s30"] = ("Trap", {})
    model, got = learn(FakeApp(chain, start="s0"), [("esc", "always reachable home from overlay"), ("n", "never overlay")], max_states=10)
    assert not model.complete and "state budget" in model.stop
    assert got["esc"].status == "vacuous" and got["n"].status == "open"


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


@pytest.mark.parametrize("viewports, ok", [('["390x844"]', True), ("[]", False)])
def test_viewports_must_name_at_least_one(tmp_path, viewports, ok):
    from telic.ui.config import ConfigError, load

    (tmp_path / "telic.toml").write_text(f'[ui]\nurl = "http://localhost:1"\nviewports = {viewports}\n')
    if ok:
        assert load(str(tmp_path / "telic.toml"), str(tmp_path)).viewports == [(390, 844)]
    else:
        with pytest.raises(ConfigError, match="viewports is empty"):
            load(str(tmp_path / "telic.toml"), str(tmp_path))
