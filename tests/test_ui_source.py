"""What the app's source adds to a UI model: the keys its handlers listen for
and the variables its handlers change that decide what renders."""

import json
import re
import shutil
from pathlib import Path

import pytest
from test_ui import needs_browser, run_ui

from telic.ui.source import scan, swift_keys

needs_node = pytest.mark.skipif(shutil.which("node") is None, reason="Node.js not available")


def keys_of(tmp_path, name, text):
    (tmp_path / name).write_text(text)
    return {k.key for k in scan(str(tmp_path)).keys}


def hidden_of(tmp_path, name, text):
    (tmp_path / name).write_text(text)
    return {h.name: h for h in scan(str(tmp_path)).hidden}


@needs_node
@pytest.mark.parametrize(
    "name, text, keys",
    [
        ("a.js", "document.addEventListener('keydown', (e) => { if (e.key === 'Escape') close(); });", {"Escape"}),
        ("a.js", "function onKey(e) { if ((e.metaKey || e.ctrlKey) && e.key === 'k') open(); }\nwindow.addEventListener('keydown', onKey);", {"ControlOrMeta+k"}),
        ("a.ts", "window.onkeydown = (e: KeyboardEvent) => { switch (e.key) { case 'ArrowUp': up(); break; case ' ': play(); } };", {"ArrowUp", "Space"}),
        ("a.js", "el.addEventListener('keyup', (e) => { if (e.keyCode === 13 && e.shiftKey) send(); });", {"Shift+Enter"}),
        ("a.js", "el.addEventListener('keydown', (e) => { if (['j', 'k'].includes(e.key.toLowerCase())) move(e.key); });", {"j", "k"}),
        ("A.tsx", "export function A() { return <div onKeyDown={(e) => { if (e.key === 'Delete') remove(); }} />; }", {"Delete"}),
        ("A.tsx", "export function A() { useHotkeys({ 'shift+?': help, 'mod+,': settings, n: add }); return <p/>; }", {"Shift+?", "ControlOrMeta+,", "n"}),
        ("a.js", "hotkeys('ctrl+k, command+k', find); Mousetrap.bind(['g i', 'esc'], home);", {"Control+k", "Meta+k", "Escape"}),
        ("A.svelte", "<script>\n  function onKey(e) { if (e.key === 'Escape') open = false }\n</script>\n<svelte:window onkeydown={onKey} />", {"Escape"}),
        ("A.svelte", "<svelte:window on:keydown={(e) => e.key === '/' && focus()} />", {"/"}),
        ("A.vue", "<template><input @keyup.enter=\"send\" @keydown.ctrl.z=\"undo\"></template>", {"Enter", "Control+z"}),
        # not key handlers: a map's key, a click handler
        ("a.js", "const m = items.filter((x) => x.key === 'Escape'); el.addEventListener('click', (e) => { if (e.key === 'q') quit(); });", set()),
    ],
)
def test_keys_a_handler_listens_for_are_found(tmp_path, name, text, keys):
    assert keys_of(tmp_path, name, text) == keys


@pytest.mark.parametrize(
    "text, keys",
    [
        ('Button("New") { add() }.keyboardShortcut("n")', {"Meta+n"}),
        ('Button("Find") { }.keyboardShortcut("f", modifiers: [.command, .shift])', {"Meta+Shift+f"}),
        ('Button("Cancel") { }.keyboardShortcut(.cancelAction)', {"Escape"}),
        (".onKeyPress(.escape) { dismiss(); return .handled }", {"Escape"}),
        ('UIKeyCommand(input: "r", modifierFlags: .command, action: #selector(reload))', {"Meta+r"}),
        ("List { }.onExitCommand { close() }", {"Escape"}),
    ],
)
def test_swift_key_commands_are_found(text, keys):
    assert {k.key for k in swift_keys(text, "App.swift")} == keys


@needs_node
@pytest.mark.parametrize(
    "name, text, hidden, not_hidden",
    [
        # a counter a handler bumps, deciding whether a button renders
        ("a.js", "let tip = 0;\nnext.addEventListener('click', () => { tip += 1; });\nhelp.addEventListener('click', () => { if (tip === 3) trap(); });", {"tip"}, set()),
        # derived through a handler's guard: `count` decides `locked`, which renders
        (
            "A.svelte",
            "<script>\n  let count = $state(0)\n  let locked = $state(false)\n  const other = 1\n  function step() { count++; if (count >= 3) locked = true }\n</script>\n<button onclick={step}>Step</button>\n{#if !locked}<button>Close</button>{/if}",
            {"count", "locked"},
            {"other"},
        ),
        # React: a setter called from a handler, the state in a condition of the render (never set: not state)
        (
            "A.tsx",
            "export function A() {\n  const [open, setOpen] = useState(false)\n  const [text, setText] = useState('')\n  return <div>{open && <Dialog />}<button onClick={() => setOpen(true)} /><input value={text} readOnly /></div>\n}",
            {"open"},
            {"text"},
        ),
        # written only where it is declared, or never read where rendering is decided
        ("A.svelte", "<script>\n  let n = $state(0)\n  let log = $state(0)\n  function f() { log++ }\n</script>\n<p>{n}</p><button onclick={f}>x</button>", set(), {"n", "log"}),
    ],
)
def test_state_handlers_change_that_decides_rendering_is_found(tmp_path, name, text, hidden, not_hidden):
    got = hidden_of(tmp_path, name, text)
    assert hidden <= set(got) and not (not_hidden & set(got))


@needs_node
def test_a_variable_a_timer_changes_is_marked(tmp_path):
    got = hidden_of(tmp_path, "a.js", "let left = 3;\nreset.addEventListener('click', () => { left = 3; });\nsetInterval(() => { left -= 1; }, 1000);\nif (left) show();")
    assert got["left"].clock and got["left"].writes


# ---------------------------------------------------------------------------
# In a browser: an app whose trap hides behind a counter the tree does not
# show, or behind a key no button offers

SOURCE_APP = Path(__file__).parent / "cases" / "ui" / "source-app"


def source_app(tmp_path, bugs=(), renamed=False):
    """The fixture app; ``renamed``: it serves a build whose variables are
    not named as in the source, so the model cannot read them."""
    d = tmp_path / "app"
    shutil.copytree(SOURCE_APP, d)
    (d / "bugs.js").write_text(f"window.BUGS = {json.dumps(list(bugs))};\n")
    if renamed:
        (d / "src").mkdir()
        (d / "app.js").rename(d / "src" / "app.js")
        (d / "dist").mkdir()
        for f in ("index.html", "bugs.js"):
            shutil.copy(d / f, d / "dist" / f)
        (d / "dist" / "app.js").write_text(re.sub(r"\btip\b", "t", (d / "src" / "app.js").read_text()))
        (d / "telic.toml").write_text((d / "telic.toml").read_text().replace('static = "."', 'static = "dist"'))
    return d


@needs_browser
@pytest.mark.parametrize(
    "bugs, renamed, status, trace",
    [
        ((), False, "proved", None),
        (("counter",), False, "refuted", ['click button "Next tip"'] * 3 + ['click button "Help"']),
        (("shortcut",), False, "refuted", ["press Shift+?"]),
        # the counter decides what renders, but the build hides it: no proof
        ((), True, "open", None),
    ],
)
def test_state_and_keys_only_the_source_shows(tmp_path, bugs, renamed, status, trace):
    rep, got = run_ui(source_app(tmp_path, bugs, renamed))
    r = got["escape"]
    assert r.status == status, r.detail
    if trace:
        assert r.trace == trace and r.replay["confirmed"]
    (m,) = rep.ui.apps[0].models
    assert m["keys"] == ["Shift+? (src/app.js:31)" if renamed else "Shift+? (app.js:31)"]
    assert bool(m["unread"]) == renamed and ("cannot see `tip`" in r.detail) == renamed
