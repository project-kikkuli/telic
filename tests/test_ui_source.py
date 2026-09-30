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
        # keys looked up in a table the source spells out
        ("a.js", "const keymap = { '?': help, Escape: close };\ndocument.addEventListener('keydown', (e) => { const f = keymap[e.key]; if (f) f(); });", {"?", "Escape"}),
        ("a.js", "const m = new Map([['k', open], ['j', down]]);\ndocument.addEventListener('keydown', (e) => m.get(e.key)?.());", {"k", "j"}),
        ("a.js", "el.addEventListener('keydown', ({ key }) => { if (key === 'Enter') send(); });", {"Enter"}),
        ("a.js", "el.addEventListener('keydown', (e) => { if (e.key !== 'Escape') return; close(); });", {"Escape"}),
        ("A.vue", "<template><div @keydown=\"$event.key === 'k' && open()\"></div></template>", {"k"}),
    ],
)
def test_keys_a_handler_listens_for_are_found(tmp_path, name, text, keys):
    assert keys_of(tmp_path, name, text) == keys


@needs_node
@pytest.mark.parametrize(
    "text, gap",
    [
        ("const keys = load();\ndocument.addEventListener('keydown', (e) => keys[e.key]?.());", "a table the source does not spell out"),
        ("el.addEventListener('keydown', (e) => { if (e.key !== 'Escape') typeahead(e.key); });", "every key but one"),
        ("el.addEventListener('keydown', (e) => { switch (e.key) { case 'a': a(); break; default: other(e.key); } });", "no case names"),
        ("import { onKey } from './keys';\nwindow.addEventListener('keydown', onKey);", "not in this file"),
        ("import { handle } from './keys';\nwindow.addEventListener('keydown', (e) => handle(e));", "another file"),
        ("const k = prefs.key;\nuseHotkeys(k, open);", "does not spell out"),
    ],
)
def test_keys_a_handler_takes_from_elsewhere_are_a_gap(tmp_path, text, gap):
    (tmp_path / "a.js").write_text(text)
    facts = scan(str(tmp_path))
    assert any(gap in g.why for g in facts.gaps), facts.gaps


@needs_node
def test_a_hotkey_function_whose_callers_spell_out_the_keys_is_no_gap(tmp_path):
    (tmp_path / "hooks.ts").write_text(
        "export function useHotkeys(bindings) {\n  window.addEventListener('keydown', (e) => { const h = bindings[e.key.toLowerCase()]; if (h) h(e); });\n}"
    )
    (tmp_path / "App.tsx").write_text("import { useHotkeys } from './hooks';\nexport function App() { useHotkeys({ '/': find }); return <p/>; }")
    facts = scan(str(tmp_path))
    assert {k.key for k in facts.keys} == {"/"} and not facts.gaps


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
@pytest.mark.parametrize(
    "files, hidden",
    [
        # a Svelte store another module declares, changed and read (`$tip`) by a component
        (
            {
                "store.js": "import { writable } from 'svelte/store'\nexport const tip = writable(0)",
                "A.svelte": "<script>\n  import { tip } from './store.js'\n</script>\n<button onclick={() => tip.update((n) => n + 1)}>Next</button>\n{#if $tip !== 3}<button>Close</button>{/if}",
            },
            {"tip"},
        ),
        # Vue refs, changed by template statements and read by v-if
        (
            {"A.vue": "<script setup>\nimport { ref } from 'vue'\nconst tip = ref(0)\n</script>\n<template><button @click=\"tip = (tip + 1) % 4\">Next</button><p v-if=\"tip !== 3\">ok</p></template>"},
            {"tip"},
        ),
        # an object one module declares and another's handler changes
        (
            {
                "state.js": "export const state = { tip: 0 };",
                "app.js": "import { state } from './state.js';\nnext.addEventListener('click', () => { state.tip += 1; });\nhelp.addEventListener('click', () => dialog(state.tip !== 3));",
            },
            {"state"},
        ),
        # what the page keeps in storage
        ({"app.js": "next.addEventListener('click', () => localStorage.setItem('tip', '1'));"}, {"localStorage"}),
    ],
)
def test_state_that_lives_elsewhere_is_found(tmp_path, files, hidden):
    for name, text in files.items():
        (tmp_path / name).write_text(text)
    assert hidden <= {h.name for h in scan(str(tmp_path)).hidden}


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


# ---------------------------------------------------------------------------
# Hidden state the model once missed and proved escape over; each app traps
# Help once Next tip was clicked three times, or behind a key

DIALOG = """function dialog(label, closable) {
  const box = document.createElement("div");
  box.className = "modal";
  box.innerHTML = `<div role="dialog" aria-modal="true" aria-label="${label}"><p>${label}</p></div>`;
  if (closable) {
    const ok = document.createElement("button");
    ok.textContent = "Close";
    ok.addEventListener("click", () => box.remove());
    box.firstChild.append(ok);
  }
  document.body.append(box);
}
"""
LEMMA = "//@ [ESCAPE] ui escape: always reachable home from overlay\n"
NEXT = 'document.getElementById("next").addEventListener("click", '
HELP = 'document.getElementById("help").addEventListener("click", '


@needs_browser
@pytest.mark.parametrize(
    "files, module, status",
    [
        # kept in localStorage, not a variable
        ({"app.js": NEXT + '() => localStorage.setItem("tip", String((Number(localStorage.getItem("tip") || 0) + 1) % 4)));\n' + HELP + '() => dialog("Help", Number(localStorage.getItem("tip")) !== 3));'}, False, "refuted"),
        # a key looked up in a table
        ({"app.js": 'const keymap = { "?": () => dialog("Shortcuts", false) };\ndocument.addEventListener("keydown", (e) => { const f = keymap[e.key]; if (f && !document.querySelector(".modal")) f(); });\n' + HELP + '() => dialog("Help", true));'}, False, "refuted"),
        # a timer also writes it
        ({"app.js": "let tip = 0;\n" + NEXT + "() => { tip = (tip + 1) % 4; });\nsetInterval(() => { if (tip > 3) tip = 0; }, 3600000);\n" + HELP + '() => dialog("Help", tip !== 3));'}, False, "refuted"),
        # a global the reader cannot see, and a closure's variable of the same name it can
        ({"app.js": "var tip = 0;\n" + NEXT + "() => { tip = (tip + 1) % 4; });\n" + HELP + '() => dialog("Help", tip !== 3));\nfunction hint(el) {\n  let tip = "hint";\n  el.addEventListener("mouseover", () => { el.title = tip; });\n}\nhint(document.getElementById("help"));'}, False, "open"),
        # another module's object, changed by this one's handler
        ({"state.js": "export const state = { tip: 0 };", "app.js": 'import { state } from "./state.js";\n' + NEXT + "() => { state.tip = (state.tip + 1) % 4; });\n" + HELP + '() => dialog("Help", state.tip !== 3));'}, True, "open"),
    ],
)
def test_hidden_state_the_model_cannot_follow_is_never_proved(tmp_path, files, module, status):
    d = source_app(tmp_path)
    (d / "dialog.js").write_text(DIALOG)
    for name, text in files.items():
        (d / name).write_text((LEMMA if name == "app.js" else "") + text + "\n")
    html = (d / "index.html").read_text().replace('<script src="bugs.js"></script>', '<script src="dialog.js"></script>')
    (d / "index.html").write_text(html.replace('<script src="app.js">', '<script type="module" src="app.js">') if module else html)
    _, got = run_ui(d)
    assert got["escape"].status == status, got["escape"].detail
