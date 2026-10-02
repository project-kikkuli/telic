"""UI lemmas: the grammar, learning a model from a running app, the verdicts
and what they rest on, and the fixture web app with known-good and known-bad
variants driven through a real browser."""

import json
import shutil
import subprocess
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
    assert by["untagged"].aims == () and by["untagged"].problem is None
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

    def probe(state, snap, d, paths):
        for lem in s.lemmas:
            if lem.prop.kind == "unobscured" and lem.prop.cond.eval(snap, ex.model.home):
                occl[lem.name].record(state.id, *hit_test(d, lem.prop.goal, snap), paths)

    ex = Explorer([app], atoms.preds, Settings(keys=(), workers=1, **kw), "fake", probe)
    model = ex.learn()
    mc = ModelCheck(ex, atoms, occl)
    return model, {lem.name: mc.check(lem) for lem in s.lemmas}


def test_every_overlay_can_be_left():
    model, got = learn(FakeApp(SCREENS), [("esc", "always reachable home from overlay"), ("about", 'reachable screen "/about"')])
    assert model.complete and len(model.states) == 4
    assert got["esc"].status == "tested" and "into 2/2 states" in got["esc"].detail
    assert got["about"].status == "tested" and got["about"].trace == ['click button "About"']


def test_a_trap_is_model_only_without_a_refinement_proof():
    screens = dict(SCREENS, **{"about:help": ("Help", {})})
    _, got = learn(FakeApp(screens), [("esc", "always reachable home from overlay")])
    o = got["esc"]
    assert o.status == "open" and o.replay["confirmed"] and "model-only" in o.detail
    assert o.trace == ['click button "About"', 'click button "Help"']
    assert 'dialog "Help"' in o.detail


def test_a_covered_close_button_is_no_way_out():
    _, got = learn(FakeApp(SCREENS, covered={"Got it"}), [("esc", "always reachable home from overlay")])
    assert got["esc"].status == "open" and "covered by div.backdrop" in got["esc"].detail


def test_absence_from_a_complete_learned_graph_is_still_open():
    screens = {"home": (None, {"About": "about"}), "about": (None, {"Back": "home"})}
    _, got = learn(FakeApp(screens), [("esc", "always reachable home from overlay"), ("n", 'never button "Back" while overlay'), ("u", 'unobscured button "Save"')])
    assert {k: o.status for k, o in got.items()} == {"esc": "open", "n": "open", "u": "open"}


def test_invariants_and_occlusion():
    _, got = learn(
        FakeApp(SCREENS, menu_covered={"about"}),
        [("no-close", 'never button "Close" while not overlay'), ("help-only-on-about", 'always screen "/about" while overlay "Help"'), ("menu", 'unobscured button "Menu"')],
    )
    assert got["no-close"].status == "tested" and got["help-only-on-about"].status == "tested"
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
    assert got["esc"].status == "tested" and got["tip"].status == "tested"


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
    assert {k: r.status for k, r in got.items()} == {"escape": "tested", "dark-mode-shown": "tested", "dark-mode": "tested", "menu-visible": "tested"}
    assert {i.id: i.status for i in rep.aims} == {"ESCAPE": "partial", "SETTINGS": "partial", "NAV": "partial"}
    (m,) = rep.ui.apps[0].models
    assert m["complete"] and m["states"] > 5
    # Nothing the app is built from changed: the verdicts come from the cache.
    rep, again = run_ui(d)
    assert all(r.cached for r in again.values()) and rep.ui.apps[0].cached
    (d / "app.js").write_text((d / "app.js").read_text() + "\n// touched\n")
    _, third = run_ui(d)
    assert not any(r.cached for r in third.values())


@pytest.mark.parametrize(
    "bug, lemma, status, says",
    [
        ("trap", "escape", "open", "model-only"),
        ("forget", "dark-mode", "refuted", "reopened the app: unchecked"),
    ],
)
@needs_browser
def test_fixture_bugs_keep_counterexamples_at_their_evidence_level(tmp_path, bug, lemma, status, says):
    d = fixture_app(tmp_path, [bug])
    rep, got = run_ui(d)
    r = got[lemma]
    assert r.status == status and says in r.detail and r.replay["confirmed"] and r.trace
    assert {k for k, x in got.items() if x.status == "refuted"} == ({lemma} if status == "refuted" else set())
    assert not rep.ok


@needs_browser
def test_a_banner_that_covers_the_menu_on_phones_only(tmp_path):
    d = fixture_app(tmp_path, ["banner"], viewports=("390x844", "1280x800"))
    _, got = run_ui(d)
    r = got["menu-visible"]
    assert r.status == "refuted" and "at 390x844" in r.detail and 'div.banner "We use cookies"' in r.detail
    assert [v["status"] for v in r.viewports] == ["refuted", "tested"]


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


@pytest.mark.parametrize(
    "property, status, method, want",
    [
        ("reachable home", "proved", "witness replayed", "tested"),
        ("reachable home", "proved", "source proof", "tested"),
        ("reachable home", "proved", None, "tested"),
        ("reachable home", "refuted", "learned model", "open"),
        ("always reachable home from overlay", "refuted", "learned model", "open"),
        ('never overlay "Help"', "refuted", "learned model", "refuted"),
    ],
)
def test_cached_ui_evidence_keeps_its_level(property, status, method, want):
    from telic.ui.run import _result

    scan = Scan()
    scan_source(f"//@ [A] ui home: {property}", "app.ts", scan)
    lemma = scan.lemmas[0]
    old = {"status": status, "method": method, "detail": "old cached result", "viewports": [{"status": status}]}
    got = _result(lemma, "telic.toml", old)
    assert got.status == want and [v["status"] for v in got.viewports] == [want]
    if want == "open":
        assert "model-only" in got.detail
    if want == "tested":
        assert "proved" not in got.detail


def _static_source_case(tmp_path, app, property, stylesheet="", modules=None):
    from telic.ui.config import load
    from telic.ui.run import run
    from telic.ui.static import extract

    example = Path(__file__).parents[1] / "examples" / "ui" / "notes-react"
    node_modules = example / "node_modules"
    if not node_modules.is_dir():
        pytest.skip("source UI cases need the installed, locked notes-react Vite toolchain")
    project = tmp_path / "vite-app"
    shutil.rmtree(project, ignore_errors=True)
    shutil.copytree(example, project, ignore=shutil.ignore_patterns("node_modules", ".telic", "dist"))
    (project / "node_modules").symlink_to(node_modules.resolve(), target_is_directory=True)
    (project / "src" / "App.tsx").write_text(app)
    for path, text in (modules or {}).items():
        target = project / "src" / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    (project / "src" / "main.tsx").write_text(
        'import { createRoot } from "react-dom/client";\n'
        'import App from "./App";\n'
        'import "./index.css";\n'
        'createRoot(document.getElementById("root")!).render(<App />);\n'
    )
    (project / "src" / "index.css").write_text(stylesheet)
    (project / "index.html").write_text('<!doctype html><html><head><title>Source UI</title></head><body><div id="root"></div><script type="module" src="/src/main.tsx"></script></body></html>')
    scan = Scan()
    source_path = "vite-app/src/App.tsx"
    scan_source(f"//@ ui source: {property}", source_path, scan)
    root = str(tmp_path)
    cfg = load(str(project / "telic.toml"), root)
    model, identity, why = extract(
        str(project), root, "index.html", "vite-react", config_path=str(project / "telic.toml"),
        command=cfg.command, config_digest=cfg.digest(),
    )
    got = run(scan, root, enabled=False).results[0]
    return model, identity, why, got


def test_source_ui_does_not_prove_raw_tsx_from_a_static_server(tmp_path):
    from telic.ui.static import StaticOutcome, extract

    (tmp_path / "App.tsx").write_text('''import { useState } from "react";
export default function App() {
  const [open, setOpen] = useState(true);
  return <main>{open ? <div role="dialog" aria-label="Help"><button onClick={() => setOpen(false)}>Close</button></div> : <h1>Home</h1>}</main>;
}''')
    (tmp_path / "main.tsx").write_text('import { createRoot } from "react-dom/client"; import App from "./App"; createRoot(document.getElementById("root")!).render(<App />);')
    (tmp_path / "index.html").write_text('<body><div id="root"></div><script type="module" src="/main.tsx"></script></body>')
    model, identity, why = extract(str(tmp_path), str(tmp_path))
    got = StaticOutcome("open", "source model", why or "no executable app provenance")
    assert model is None and why and "cannot execute TypeScript or JSX" in why
    assert got.status == "open" and got.method == "source model"


def test_source_ui_does_not_prove_an_unmounted_export(tmp_path):
    from telic.ui.static import extract

    (tmp_path / "App.tsx").write_text(
        'import { useState } from "react";\n'
        'export default function App() { const [open] = useState(true); return open ? <button>Save</button> : null; }\n'
    )
    model, _, why = extract(str(tmp_path), str(tmp_path))
    assert model is None and why and "verified React createRoot" in why


def test_source_ui_requires_html_to_load_the_mounted_entry(tmp_path):
    from telic.ui.config import load
    from telic.ui.static import extract

    _static_source_case(
        tmp_path,
        'import { useState } from "react"; export default function App() { const [open] = useState(true); return open ? <button>Save</button> : null; }',
        'reachable button "Save"',
    )
    project = tmp_path / "vite-app"
    (project / "index.html").write_text('<body><div id="root"></div></body>')
    cfg = load(str(project / "telic.toml"), str(tmp_path))
    model, _, why = extract(str(project), str(tmp_path), "index.html", "vite-react", config_path=str(project / "telic.toml"), command=cfg.command, config_digest=cfg.digest())
    assert model is None and why and ("does not connect a #root root" in why or "cannot execute TypeScript or JSX" in why)


def test_source_ui_refutes_a_modal_close_handler_that_keeps_it_open(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [open, setOpen] = useState(true);
  return open ? <div role="dialog" aria-label="Help"><button onClick={() => setOpen(true)}>Close</button></div> : <h1>Home</h1>;
}''',
        'always reachable home from overlay "Help"',
    )
    assert why is None and got.status == "refuted" and got.method == "source proof"


def test_source_ui_rejects_a_shadowed_fake_react_hook(tmp_path):
    _, _, why, _ = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  function useState(_seed: boolean) { return [false, () => {}] as const; }
  const [open] = useState(true);
  return open ? <button>Save</button> : <p>Closed</p>;
}''',
        'reachable button "Save"',
    )
    assert why and "unshadowed React useState import" in why


def test_source_ui_rejects_loose_equality_and_effects(tmp_path):
    _, _, why, _ = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [open] = useState(true);
  return open == true ? <button>Save</button> : <p>Closed</p>;
}''',
        'reachable button "Save"',
    )
    assert why and "operator outside the finite UI expression model" in why
    _, _, why, _ = _static_source_case(
        tmp_path,
        '''import { useEffect, useState } from "react";
export default function App() {
  const [open] = useState(true);
  useEffect(() => {}, []);
  return open ? <button>Save</button> : <p>Closed</p>;
}''',
        'reachable button "Save"',
    )
    assert why and "outside the source UI model" in why


def test_source_ui_rejects_native_controls(tmp_path):
    _, _, why, _ = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [ready] = useState(true);
  return ready ? <input aria-label="Search" /> : null;
}''',
        'reachable textbox "Search"',
    )
    assert why and "native input behavior is outside the source UI model" in why


def test_source_ui_treats_aria_hidden_string_as_hidden(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [open] = useState(true);
  return open ? <button aria-hidden="true">Secret</button> : <p>Closed</p>;
}''',
        'reachable button "Secret"',
    )
    assert why is None and got.status == "refuted" and got.method == "source proof"


def test_source_ui_uses_native_implicit_roles(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [ready] = useState(true);
  return ready ? <main><p>Home</p></main> : null;
}''',
        'never main',
    )
    assert why is None and got.status == "refuted" and got.method == "source proof"


def test_source_ui_models_child_then_parent_click_updates(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [open, setOpen] = useState(true);
  return open ? <div role="dialog" aria-label="Help" onClick={() => setOpen(false)}><button onClick={() => { setOpen(false); setOpen(true); }}>Close</button></div> : <h1>Home</h1>;
}''',
        'always reachable home from overlay "Help"',
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_bubbles_after_a_child_handler_returns(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [open, setOpen] = useState(true);
  return open ? <div role="dialog" aria-label="Help" onClick={() => setOpen(false)}><button onClick={() => { return; setOpen(true); }}>Close</button></div> : <h1>Home</h1>;
}''',
        'always reachable home from overlay "Help"',
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_models_click_handlers_on_aria_disabled_controls(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [open, setOpen] = useState(true);
  return open ? <div role="dialog" aria-label="Help"><button aria-disabled="true" onClick={() => setOpen(false)}>Close</button></div> : <h1>Home</h1>;
}''',
        'always reachable home from overlay "Help"',
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_tracks_dynamic_jsx_names_and_functional_state_updates(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App() {
  const [open, setOpen] = useState(true);
  return <button onClick={() => setOpen((wasOpen) => !wasOpen)}>{open ? "Close" : "Open"}</button>;
}''',
        'reachable button "Open"',
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


@pytest.mark.parametrize(
    "body, expected, reason",
    [
        ('const [open]=useState(false); if(open) return <button>Save</button>;', 'reachable button "Save"', "refuted"),
        ('const [open]=useState(true); throw new Error("boom"); return <button>Save</button>;', 'reachable button "Save"', "open"),
    ],
)
def test_source_ui_respects_component_returns_and_render_failures(tmp_path, body, expected, reason):
    model, _, why, got = _static_source_case(
        tmp_path,
        'import { useState } from "react"; export default function App(){' + body + '}',
        expected,
    )
    if reason == "open":
        assert model is None and why and "control flow" in why and got.status == "open"
    else:
        assert why is None and got.status == "refuted" and got.method == "source proof"


def test_source_ui_keeps_physical_clicks_on_aria_hidden_controls(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App(){const [open,setOpen]=useState(false);return <main><button aria-hidden="true" onClick={()=>setOpen(true)}>Open</button>{open?<div role="dialog" aria-label="Help"/>:null}</main>}''',
        'never overlay "Help"',
    )
    assert why is None and got.status == "refuted" and got.method == "source proof"


def test_source_ui_uses_child_to_parent_bubbling_order(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App(){const [open,setOpen]=useState(true);return open?<div role="dialog" aria-label="Help" onClick={()=>setOpen(true)}><div onClick={()=>setOpen(false)}><button onClick={()=>setOpen(true)}>Close</button></div></div>:<h1>Home</h1>}''',
        'reachable heading "Home"',
    )
    assert why is None and got.status == "refuted" and got.method == "source proof"


def test_source_ui_does_not_bind_event_parameters_to_captured_state(tmp_path):
    model, _, why, _ = _static_source_case(
        tmp_path,
        '''import { useState } from "react";
export default function App(){const [open,setOpen]=useState(false);return <button onClick={(open)=>setOpen(!open)}>Open</button>}''',
        'reachable heading "Home"',
    )
    assert model is None and why and "event parameter" in why


@pytest.mark.parametrize(
    "app, property, status",
    [
        ('<button><span hidden>Secret</span>Save</button>', 'reachable button "SecretSave"', "refuted"),
        ('<div aria-label="Named">Hello</div>', 'reachable generic "Named"', "refuted"),
        ('<button>A &amp; B</button>', 'reachable button "A & B"', "proved"),
        ('<button>{open && <span>Hello</span>}Save</button>', 'reachable button "0Save"', "proved"),
        ('<button>{open && <span>Hello</span>}Save</button>', 'reachable button "Save"', "refuted"),
    ],
)
def test_source_ui_matches_accessible_names_and_react_rendering(tmp_path, app, property, status):
    _, _, why, got = _static_source_case(
        tmp_path,
        'import { useState } from "react"; export default function App(){const [open]=useState(0);return ' + app + ';}',
        property,
    )
    assert why is None and got.status == status and got.method == "source proof"


def test_source_ui_models_imported_css_visibility(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        'import { useState } from "react"; export default function App(){const [ready]=useState(true);return <main><button className="off">Hidden</button><button className="on">Shown</button></main>}',
        'reachable button "Hidden"',
        ".off { display: none; } .on { visibility: visible; }",
    )
    assert why is None and got.status == "refuted" and got.method == "source proof"


def test_source_ui_inlines_imported_stateless_components(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        'import { useState } from "react"; import { HelpPanel } from "./HelpPanel"; export default function App(){const [ready]=useState(true);return ready ? <main><HelpPanel /></main> : null;}',
        'reachable button "Close"',
        modules={"HelpPanel.tsx": 'export function HelpPanel(){return <div role="dialog" aria-label="Help"><button>Close</button></div>}\n'},
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_proves_deterministic_root_without_hooks(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        'export default function App(){return <main><h1>Notes</h1><button>Menu</button></main>}',
        'reachable button "Menu"',
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_binds_imported_component_props_and_handlers(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        'import { useState } from "react"; import { HelpPanel } from "./HelpPanel"; export default function App(){const [open,setOpen]=useState(true);return <main>{open ? <HelpPanel title="Help" onClose={() => setOpen(false)} /> : <h1>Home</h1>}</main>}',
        'always reachable home from overlay "Help"',
        modules={"HelpPanel.tsx": 'export function HelpPanel({title,onClose}:{title:string,onClose:()=>void}){return <div role="dialog" aria-label={title}><button onClick={onClose}>Close</button></div>}\n'},
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_composes_stateful_imports_with_finite_state(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        'import { useState } from "react"; import { HelpPanel } from "./HelpPanel"; export default function App(){const [ready]=useState(true);return <main><HelpPanel title="Help" /></main>}',
        'reachable button "Close"',
        modules={"HelpPanel.tsx": 'import {useState} from "react"; export function HelpPanel({title}:{title:string}){const [open,setOpen]=useState(false);return <div role="dialog" aria-label={title}>{open?<button>Close</button>:<button onClick={()=>setOpen(true)}>Open help</button>}</div>}\n'},
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_models_imported_forwarding_state_hooks(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        'import { useDisclosure } from "./useDisclosure"; export default function App(){const [open,setOpen]=useDisclosure(false);return open?<div role="dialog" aria-label="Help"><button onClick={()=>setOpen(false)}>Close</button></div>:<button onClick={()=>setOpen(true)}>Open help</button>}',
        'always reachable button "Open help" from overlay "Help"',
        modules={"useDisclosure.ts": 'import {useState} from "react"; export function useDisclosure(initial:boolean){const [value,setValue]=useState(initial);return [value,setValue] as const;}\n'},
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_preserves_caller_children_through_imported_layouts(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        'import {useState} from "react"; import {Frame} from "./Frame"; export default function App(){const [open,setOpen]=useState(true);return <Frame>{open?<div role="dialog" aria-label="Help"><button onClick={()=>setOpen(false)}>Close</button></div>:<h1>Home</h1>}</Frame>}',
        'always reachable heading "Home" from overlay "Help"',
        modules={"Frame.tsx": 'import type {ReactNode} from "react"; export function Frame({children}:{children:ReactNode}){return <main>{children}</main>}\n'},
    )
    assert why is None and got.status == "proved" and got.method == "source proof"


def test_source_ui_rejects_conditional_mount_of_stateful_children(tmp_path):
    _, _, why, got = _static_source_case(
        tmp_path,
        'import {useState} from "react"; import {Frame} from "./Frame"; import {Counter} from "./Counter"; export default function App(){const [show]=useState(true);return <Frame show={show}><Counter /></Frame>}',
        'reachable button "Increment"',
        modules={
            "Frame.tsx": 'export function Frame({show,children}:{show:boolean,children:React.ReactNode}){return show?<main>{children}</main>:null}\n',
            "Counter.tsx": 'import {useState} from "react"; export function Counter(){const [n,setN]=useState(0);return <button onClick={()=>setN(n+1)}>Increment</button>}\n',
        },
    )
    assert why and "stateful children have a conditional mount" in why
    assert got.status == "open" and got.method != "source proof"


@pytest.mark.parametrize(
    "html",
    [
        '<body hidden><div id="root"></div><script type="module" src="/main.tsx"></script></body>',
        '<body style="display:none"><div id="root"></div><script type="module" src="/main.tsx"></script></body>',
        '<head><button>Other</button></head><body><div id="root"></div><script type="module" src="/main.tsx"></script></body>',
        '<body><div id="root"></div><script type="application/json" src="/main.tsx"></script></body>',
    ],
)
def test_source_ui_rejects_hidden_reparsed_or_non_executable_html(tmp_path, html):
    from telic.ui.config import load
    from telic.ui.run import run
    from telic.ui.static import extract

    _static_source_case(
        tmp_path,
        'import { useState } from "react"; export default function App(){const [ready]=useState(true);return <button>Save</button>}',
        'reachable button "Save"',
    )
    project = tmp_path / "vite-app"
    (project / "index.html").write_text(html.replace("/main.tsx", "/src/main.tsx"))
    cfg = load(str(project / "telic.toml"), str(tmp_path))
    model, _, why = extract(
        str(project), str(tmp_path), "index.html", "vite-react", config_path=str(project / "telic.toml"),
        command=cfg.command, config_digest=cfg.digest(),
    )
    scan = Scan()
    scan_source('//@ ui html: reachable button "Save"', "vite-app/src/App.tsx", scan)
    result = run(scan, str(tmp_path), enabled=False).results[0]
    assert model is None and why and "does not connect" in why
    assert result.status == "open" and result.method != "source proof"


def test_configured_source_proof_uses_the_served_static_tree(tmp_path):
    from telic.ui.run import run

    (tmp_path / "App.tsx").write_text('import { useState } from "react"; export default function App(){const [ready]=useState(true);return <button>Save</button>}')
    (tmp_path / "main.tsx").write_text('import { createRoot } from "react-dom/client"; import App from "./App"; createRoot(document.getElementById("root")!).render(<App />);')
    (tmp_path / "index.html").write_text('<body><div id="root"></div><script type="module" src="/main.tsx"></script></body>')
    (tmp_path / "site").mkdir()
    (tmp_path / "site" / "index.html").write_text('<button>Bad</button>')
    (tmp_path / "telic.toml").write_text('[ui]\nstatic="site"\n')
    scan = Scan()
    scan_source('//@ ui configured: reachable button "Save"', "App.tsx", scan)
    rep = run(scan, str(tmp_path), enabled=False)
    assert rep.results[0].status == "open" and rep.results[0].method != "source proof"


def test_configured_static_url_selects_the_served_html_entry(tmp_path):
    from telic.ui.run import run

    site = tmp_path / "site"
    site.mkdir()
    (site / "App.tsx").write_text('import { useState } from "react"; export default function App(){const [ready]=useState(true);return <button>Save</button>}')
    (site / "main.tsx").write_text('import { createRoot } from "react-dom/client"; import App from "./App"; createRoot(document.getElementById("root")!).render(<App />);')
    (site / "index.html").write_text('<body><div id="root"></div><script type="module" src="/main.tsx"></script></body>')
    (site / "other.html").write_text('<body><button>Other</button></body>')
    (tmp_path / "telic.toml").write_text('[ui]\nstatic="site"\nurl="/other.html"\n')
    scan = Scan()
    scan_source('//@ ui configured: reachable button "Save"', "site/App.tsx", scan)
    rep = run(scan, str(tmp_path), enabled=False)
    assert rep.results[0].status == "open" and rep.results[0].method != "source proof"


@pytest.mark.parametrize(
    "js, expr, expected",
    [
        ("true === 1", ["bin", "eq", ["lit", True], ["lit", 1]], False),
        ('"a" + "b"', ["bin", "add", ["lit", "a"], ["lit", "b"]], "ab"),
        ('"\\u{10000}" < "\\uE000"', ["bin", "lt", ["lit", "\U00010000"], ["lit", "\uE000"]], True),
        ('false || "fallback"', ["bin", "or", ["lit", False], ["lit", "fallback"]], "fallback"),
        ("null === false", ["bin", "eq", ["lit", None], ["lit", False]], False),
        ("6 % 4", ["bin", "mod", ["lit", 6], ["lit", 4]], 2),
    ],
)
def test_source_expression_model_matches_node_for_accepted_values(js, expr, expected):
    from telic.frontend import typescript
    from telic.ui.static import _eval

    typescript.ensure_installed()
    script = "let s='';process.stdin.on('data',x=>s+=x);process.stdin.on('end',()=>process.stdout.write(JSON.stringify(Function('return ('+JSON.parse(s)+')')())));"
    node = subprocess.run([typescript._node(), "-e", script], input=json.dumps(js), capture_output=True, text=True, check=True)
    assert json.loads(node.stdout) == expected == _eval(expr, {})


def test_source_expression_model_rejects_coercion_and_unsafe_intermediates():
    from telic.ui.static import _eval

    with pytest.raises(ValueError, match="addition coercion"):
        _eval(["bin", "add", ["lit", None], ["lit", True]], {})
    with pytest.raises(ValueError, match="exact integer range"):
        _eval(["bin", "add", ["lit", 2**53 - 1], ["lit", 1]], {})


def test_screens_abstraction_keeps_only_what_the_lemmas_see():
    # a wizard on one screen the lemmas do not look into: each step shows other controls
    steps = "ABCDEFGHIJ"
    screens = {f"home:{c}": (None, {f"Step {c}": f"home:{steps[min(i + 1, 9)]}"}) for i, c in enumerate(steps)}
    fine, _ = learn(FakeApp(screens, start="home:A"), [("r", "reachable home")])
    coarse, got = learn(FakeApp(screens, start="home:A"), [("r", "reachable home")], abstraction="screens")
    assert len(fine.states) == 10 and len(coarse.states) == 1 and coarse.complete
    assert got["r"].status == "tested"


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
    assert got["escape"].status == "tested", got["escape"].detail
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
        ('unobscured button "Save"', '<div style="height:80px;overflow:auto"><div style="height:600px"></div><button>Save</button></div>', "", "", "tested", ""),
        ('unobscured button "Menu"', MENU + "<div class=veil>Sale</div>", "", ".veil{position:fixed;top:0;left:0;width:300px;height:90px;background:#c00;pointer-events:none}", "refuted", "painted over it"),
        ('unobscured button "Menu"', MENU + "<div class=veil></div>", "", ".veil{position:fixed;inset:0;pointer-events:none}", "tested", ""),
        ('unobscured button "Menu"', MENU + '<div role=dialog aria-label="Cookies" class=ban>We use cookies</div>', "", ".ban{position:fixed;top:0;left:0;right:0;height:60px;background:#fd0}", "refuted", "Cookies"),
        ('unobscured button "Menu" while not overlay', MENU + '<div class=bd><div role=dialog aria-modal=true aria-label="Hi">Hi</div></div>', "", ".bd{position:fixed;inset:0;background:#0006}", "open", ""),
        # a dialog titled by its heading is named as a screen reader names it (two such dialogs are not one state)
        ('reachable overlay "Delete item?"', '<button onclick="document.querySelector(\'main\').insertAdjacentHTML(\'beforeend\', \'<div role=dialog aria-labelledby=t><h2 id=t>Delete item?</h2></div>\')">Delete</button>', "", "", "tested", "reached in 1 step"),
        ('never overlay "Expired"', "<p>Hi</p>", "setTimeout(() => document.querySelector('main').insertAdjacentHTML('beforeend', '<div role=dialog aria-label=Expired>Expired</div>'), 1500);", "", "refuted", "Expired"),
    ],
)
@needs_browser
def test_what_a_person_sees_and_can_reach(tmp_path, lemma, body, js, css, status, says):
    _, got = run_ui(tiny_app(tmp_path, lemma, body, js, css))
    assert (got["x"].status, says in got["x"].detail) == (status, True), got["x"].detail
