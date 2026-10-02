"""Source-connected finite UI models for a conservative React subset."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
from collections import deque
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path
from typing import Any

from ..frontend import typescript
from . import source
from .spec import Pred, Prop, Target, UiLemma
from .tree import Node, Snapshot

EXTRACTOR = Path(__file__).resolve().parent.parent / "frontend" / "ts" / "uistatic.mjs"
MAX_STATES = 4096
ARIA_ROLES = {"alert", "alertdialog", "application", "article", "banner", "blockquote", "button", "caption", "cell", "checkbox", "code", "columnheader", "combobox", "complementary", "contentinfo", "definition", "deletion", "dialog", "document", "emphasis", "feed", "figure", "form", "generic", "grid", "gridcell", "group", "heading", "img", "insertion", "link", "list", "listbox", "listitem", "log", "main", "mark", "marquee", "math", "menu", "menubar", "menuitem", "menuitemcheckbox", "menuitemradio", "meter", "navigation", "note", "option", "paragraph", "progressbar", "radio", "radiogroup", "region", "row", "rowgroup", "rowheader", "scrollbar", "search", "searchbox", "separator", "slider", "spinbutton", "status", "strong", "subscript", "superscript", "switch", "tab", "table", "tablist", "tabpanel", "term", "textbox", "timer", "toolbar", "tooltip", "tree", "treegrid", "treeitem"}


@dataclass
class StaticOutcome:
    status: str
    method: str
    detail: str
    trace: list[str] | None = None
    source: list[str] | None = None
    receipt: dict[str, Any] | None = None


def extract(top: str, root: str) -> tuple[dict[str, Any] | None, str | None, str | None]:
    """Return one statically extractable app and the identity of its source closure."""
    files = source._files(top, source.WEB_EXT)
    if not files:
        return None, None, "no TypeScript or JavaScript app source was found"
    css = []
    html = []
    for directory, dirs, names in os.walk(top):
        dirs[:] = sorted(d for d in dirs if d not in source.SKIP_DIRS and not d.startswith("."))
        css.extend(os.path.join(directory, n) for n in names if Path(n).suffix in (".css", ".scss", ".sass", ".less", ".styl"))
        html.extend(os.path.join(directory, n) for n in names if Path(n).suffix.lower() in (".html", ".htm"))
    if css:
        return None, None, f"CSS can change the accessibility tree ({os.path.relpath(css[0], root)}); layout/style semantics are not modeled"
    entries = []
    dig = hashlib.sha256()
    for full in files:
        try:
            data = Path(full).read_bytes()
            text = data.decode("utf-8")
        except (OSError, UnicodeDecodeError) as e:
            return None, None, f"cannot read app source {os.path.relpath(full, root)}: {e}"
        rel = os.path.relpath(full, root)
        entries.append({"path": rel.replace(os.sep, "/"), "text": text})
        dig.update(rel.encode() + b"\0" + data + b"\0")
    html_documents: list[tuple[set[str], set[str], bool, list[tuple[str, str | None, int, set[str]]], bool]] = []
    html_deps = []
    class IdParser(HTMLParser):
        def __init__(self) -> None:
            super().__init__(convert_charrefs=True)
            self.ids: set[str] = set()
            self.scripts: set[str] = set()
            self.active_script = False
            self.active_script_inline = False
            self.invalid_script = False
            self.invalid_markup = False
            self.in_body = False
            self.body_elements: list[tuple[str, str | None, int, set[str]]] = []
            self.stack: list[str] = []

        def handle_starttag(self, _tag: str, attrs: list[tuple[str, str | None]]) -> None:
            values = dict(attrs)
            if values.get("id") is not None:
                self.ids.add(values["id"] or "")
            if _tag == "body":
                self.in_body = True
                self.stack = ["body"]
                return
            elif self.in_body and _tag != "script":
                depth = max(0, len(self.stack) - 1)
                self.body_elements.append((_tag, values.get("id"), depth, set(values)))
            if _tag == "style" or (_tag == "link" and "stylesheet" in (values.get("rel") or "").lower().split()):
                self.invalid_markup = True
            if _tag != "script":
                if self.in_body and _tag not in {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}:
                    self.stack.append(_tag)
                return
            self.active_script = True
            src = values.get("src")
            kind = (values.get("type") or "").lower()
            self.active_script_inline = not src and kind not in ("application/json", "application/ld+json", "importmap")
            if src:
                self.scripts.add(os.path.normpath(src.split("?", 1)[0].lstrip("/")))

        def handle_data(self, data: str) -> None:
            if self.active_script and self.active_script_inline and data.strip():
                self.invalid_script = True
            elif self.in_body and not self.active_script and data.strip():
                self.invalid_markup = True

        def handle_endtag(self, tag: str) -> None:
            if tag == "script":
                self.active_script = False
                self.active_script_inline = False
            if tag == "body":
                self.in_body = False
                self.stack = []
            elif tag in self.stack:
                self.stack = self.stack[:self.stack.index(tag)]
    for full in sorted(html):
        try:
            data = Path(full).read_bytes()
            text = data.decode("utf-8")
        except (OSError, UnicodeDecodeError) as e:
            return None, None, f"cannot read app HTML {os.path.relpath(full, root)}: {e}"
        rel = os.path.relpath(full, root).replace(os.sep, "/")
        html_deps.append(rel)
        dig.update(rel.encode() + b"\0" + data + b"\0")
        parser = IdParser()
        parser.feed(text)
        html_documents.append((parser.ids, parser.scripts, parser.invalid_script, parser.body_elements, parser.invalid_markup))
    try:
        typescript.ensure_installed()
        got = subprocess.run(
            [typescript._node(), str(EXTRACTOR)],
            input=json.dumps({"files": entries}),
            capture_output=True,
            text=True,
            timeout=120,
            check=False,
        )
        if got.returncode:
            return None, None, got.stderr.strip() or "the TypeScript source extractor failed"
        parsed = json.loads(got.stdout)
    except (typescript.FrontendUnavailable, subprocess.SubprocessError, OSError, ValueError) as e:
        return None, None, f"cannot extract source UI behavior: {e}"
    version = (EXTRACTOR.parent / "node_modules" / "typescript" / "package.json").read_bytes()
    identity = hashlib.sha256(version + EXTRACTOR.read_bytes() + Path(__file__).read_bytes() + dig.digest()).hexdigest()
    models = parsed.get("models", [])
    if len(models) != 1:
        why = parsed.get("errors", [])
        if why:
            return None, identity, "; ".join(why)
        return None, identity, f"expected one exported React app component in the source closure, found {len(models)}"
    if parsed.get("errors"):
        return None, identity, "; ".join(parsed["errors"])
    root_id, entry = models[0].get("mountRoot"), os.path.normpath(models[0].get("mountEntry", ""))
    def hosts_model(ids: set[str], scripts: set[str], invalid_script: bool, body: list[tuple[str, str | None, int, set[str]]], invalid_markup: bool) -> bool:
        hosts = [x for x in body if x[1] == root_id]
        visible = [x for x in body if x[0] != "script"]
        if invalid_script or invalid_markup or scripts != {entry} or len(hosts) != 1 or visible != hosts:
            return False
        tag, _, depth, attrs = hosts[0]
        return tag == "div" and depth == 0 and attrs <= {"id", "class"}
    if not any(hosts_model(*document) for document in html_documents):
        return None, identity, f"static app HTML does not connect a #{root_id} root to the mounted entry {entry}"
    models[0]["dependencies"] = sorted([*(e["path"] for e in entries), *html_deps])
    return models[0], identity, None


def check(model: dict[str, Any], identity: str, lem: UiLemma) -> StaticOutcome:
    if lem.prop is None:
        return StaticOutcome("open", "source model", "the UI property could not be parsed")
    try:
        states, edges, snaps = _graph(model)
    except ValueError as e:
        return StaticOutcome("open", "source model", str(e))
    prop = lem.prop
    if prop.kind in ("unobscured", "persists"):
        return StaticOutcome("open", "source model", f"{prop.kind} needs {('CSS/layout geometry' if prop.kind == 'unobscured' else 'a storage/reopen model')}; it is not inferred from rendered roles")
    paths: list[list[str] | None] = [None] * len(states)
    paths[0] = []
    q = deque([0])
    while q:
        i = q.popleft()
        for j, action in edges[i]:
            if paths[j] is None:
                paths[j] = [*(paths[i] or []), action]
                q.append(j)
    relevant = [i for i, snap in enumerate(snaps) if prop.cond.eval(snap, "home")]
    good = [i for i, snap in enumerate(snaps) if _goal(prop.goal, snap)]
    source_lines = [f"{model['path']}:{model['line']}"]
    receipt = {"source_hash": identity, "dependencies": model.get("dependencies", [])}
    if prop.kind == "reachable":
        if good:
            return StaticOutcome("proved", "source proof", f"all source-reachable finite states were closed ({len(states)} states); witness {paths[good[0]] or ['initial state']}", paths[good[0]], source_lines, receipt)
        return StaticOutcome("refuted", "source proof", f"the source model closes with no state satisfying {prop.goal}", [], source_lines, receipt)
    if prop.kind in ("always", "never"):
        bad = [i for i in relevant if _goal(prop.goal, snaps[i]) == (prop.kind == "never")]
        if bad:
            return StaticOutcome("refuted", "source proof", f"source state violates {prop}", paths[bad[0]], source_lines, receipt)
        if not relevant:
            return StaticOutcome("open", "source proof", f"{prop} has no reachable state where its condition holds", None, source_lines, receipt)
        return StaticOutcome("proved", "source proof", f"all {len(relevant)} relevant source-reachable states satisfy {prop}", None, source_lines, receipt)
    if prop.kind == "always_reachable":
        if not relevant:
            return StaticOutcome("open", "source proof", f"{prop} has no reachable source state where its condition holds", None, source_lines, receipt)
        for start in relevant:
            todo = deque([start])
            seen = {start}
            while todo and not any(_goal(prop.goal, snaps[x]) for x in seen):
                at = todo.popleft()
                for nxt, _ in edges[at]:
                    if nxt not in seen:
                        seen.add(nxt)
                        todo.append(nxt)
            if not any(_goal(prop.goal, snaps[x]) for x in seen):
                return StaticOutcome("refuted", "source proof", f"no source transition path from a state satisfying {prop.cond} reaches {prop.goal}", paths[start], source_lines, receipt)
        return StaticOutcome("proved", "source proof", f"from each of {len(relevant)} relevant states, all source transitions include a path to {prop.goal}", None, source_lines, receipt)
    return StaticOutcome("open", "source model", f"{prop.kind} is not supported by this source model")


def _goal(goal: Pred | Target, snap: Snapshot) -> bool:
    if isinstance(goal, Pred):
        return goal.eval(snap, "home")
    return bool(goal.find(snap))


def _graph(model: dict[str, Any]) -> tuple[list[dict[str, Any]], list[list[tuple[int, str]]], list[Snapshot]]:
    declarations = model["states"]
    domains = {d["name"]: {d["initial"]} for d in declarations}
    for d in declarations:
        if isinstance(d["initial"], bool):
            domains[d["name"]].update((True, False))
    def visit(stmt: Any) -> None:
        if not isinstance(stmt, list):
            return
        if stmt and stmt[0] == "set":
            name = stmt[1]
            update = stmt[2]
            def literals(node: Any) -> None:
                if isinstance(node, list):
                    if len(node) == 2 and node[0] == "lit":
                        domains[name].add(node[1])
                    else:
                        for x in node[1:]: literals(x)
            literals(update)
        for x in stmt[1:]: visit(x)
    def render_events(node: Any) -> None:
        if not isinstance(node, dict): return
        for _, handler in node.get("events", {}).items(): visit(handler)
        for child in node.get("children", []): render_events(child)
        if node.get("type") == "branch":
            render_events(node.get("yes")); render_events(node.get("no"))
    render_events(model["render"])
    state_defs = {d["name"]: {**d, "domain": domains[d["name"]]} for d in declarations}
    initial = {d["name"]: d["initial"] for d in declarations}
    for d in declarations:
        if not isinstance(d["initial"], (bool, int, str)) and d["initial"] is not None:
            raise ValueError(f"state `{d['name']}` has a non-finite initial value at {model['path']}:{d['line']}")
    states = [initial]
    indexes = {_key(initial): 0}
    edges: list[list[tuple[int, str]]] = [[]]
    snaps = [_snapshot(model["render"], initial, model)]
    q = deque([0])
    while q:
        i = q.popleft()
        current = states[i]
        for action in _actions(model["render"], current, model):
            nxt = dict(current)
            _execute(action["handler"], current, nxt, state_defs)
            for name, value in nxt.items():
                if not any(type(value) is type(candidate) and value == candidate for candidate in state_defs[name]["domain"]):
                    raise ValueError(f"state `{name}` leaves its finite source-derived domain at {model['path']}:{action['line']}")
                if isinstance(value, int) and not isinstance(value, bool) and not -(2**53 - 1) <= value <= 2**53 - 1:
                    raise ValueError(f"state `{name}` exceeds JavaScript's exact integer range at {model['path']}:{action['line']}")
            key = _key(nxt)
            j = indexes.get(key)
            if j is None:
                if len(states) >= MAX_STATES:
                    raise ValueError(f"the source state space exceeds {MAX_STATES} states; finite closure was not established")
                j = len(states)
                indexes[key] = j
                states.append(nxt)
                edges.append([])
                snaps.append(_snapshot(model["render"], nxt, model))
                q.append(j)
            edges[i].append((j, action["label"]))
    return states, edges, snaps


def _key(state: dict[str, Any]) -> tuple:
    return tuple((k, type(v).__name__, v) for k, v in sorted(state.items()))


def _eval(e: Any, state: dict[str, Any], locals_: dict[str, Any] | None = None) -> Any:
    locals_ = locals_ or {}
    if not isinstance(e, list):
        raise ValueError("source expression is malformed")
    op = e[0]
    if op == "lit":
        return e[1]
    if op == "state":
        return state[e[1]]
    if op == "local":
        return locals_[e[1]]
    if op == "un":
        v = _eval(e[2], state, locals_)
        if e[1] == "not": return not v
        if isinstance(v, bool): v = int(v)
        if not isinstance(v, int):
            raise ValueError("JavaScript unary numeric coercion is outside the source UI model")
        return -v if e[1] == "neg" else v
    if op == "if":
        return _eval(e[2] if _eval(e[1], state, locals_) else e[3], state, locals_)
    if op == "bin":
        a, b = _eval(e[2], state, locals_), _eval(e[3], state, locals_)
        same = type(a) is type(b) and a == b
        def number(v: Any) -> bool:
            return isinstance(v, int) and not isinstance(v, bool)
        def arithmetic(fn) -> int:
            if not number(a) or not number(b):
                raise ValueError("JavaScript arithmetic is modeled only for safe integer operands")
            value = fn(a, b)
            if not -(2**53 - 1) <= value <= 2**53 - 1:
                raise ValueError("JavaScript arithmetic leaves the exact integer range")
            return value
        def remainder() -> int:
            if not number(a) or not number(b) or b == 0:
                raise ValueError("JavaScript remainder is modeled only for nonzero safe integer operands")
            q = abs(a) // abs(b)
            if (a < 0) != (b < 0): q = -q
            return a - q * b
        def addition() -> Any:
            if number(a) and number(b): return arithmetic(lambda x, y: x + y)
            if type(a) is str and type(b) is str: return a + b
            raise ValueError("JavaScript addition coercion is outside the source UI model")
        def relational(fn) -> bool:
            if type(a) is type(b) and isinstance(a, str): return fn(a.encode("utf-16-be", "surrogatepass"), b.encode("utf-16-be", "surrogatepass"))
            if number(a) and number(b) or type(a) is bool and type(b) is bool: return fn(a, b)
            raise ValueError("JavaScript relational coercion is outside the source UI model")
        return {
            "eq": lambda: same, "ne": lambda: not same, "and": lambda: a and b, "or": lambda: a or b,
            "add": addition, "sub": lambda: arithmetic(lambda x, y: x - y), "mul": lambda: arithmetic(lambda x, y: x * y), "mod": remainder,
            "lt": lambda: relational(lambda x, y: x < y), "le": lambda: relational(lambda x, y: x <= y), "gt": lambda: relational(lambda x, y: x > y), "ge": lambda: relational(lambda x, y: x >= y),
        }[e[1]]()
    raise ValueError(f"source expression operator {op!r} is unsupported")


def _execute(stmt: Any, captured: dict[str, Any], updated: dict[str, Any], defs: dict[str, Any], returned: bool = False) -> bool:
    if returned:
        return True
    op = stmt[0]
    if op == "seq":
        for child in stmt[1:]:
            returned = _execute(child, captured, updated, defs, returned)
        return returned
    if op == "event":
        for handler in stmt[1:]:
            _execute(handler, captured, updated, defs)
        return False
    if op == "return":
        return True
    if op == "if":
        branch = stmt[2] if _eval(stmt[1], captured) else stmt[3]
        return _execute(branch, captured, updated, defs)
    if op == "set":
        name, update = stmt[1], stmt[2]
        if update[0] == "functional":
            value = _eval(update[2], captured, {update[1]: updated[name]})
        else:
            value = _eval(update[1], captured)
        updated[name] = value
        return False
    raise ValueError(f"source statement {op!r} is unsupported")


def _actions(tree: dict[str, Any], state: dict[str, Any], model: dict[str, Any]) -> list[dict[str, Any]]:
    out = []
    def visit(n: dict[str, Any], ancestors: list[Any] | None = None) -> None:
        ancestors = ancestors or []
        kind = n["type"]
        if kind in ("empty", "text"):
            return
        if kind == "group":
            for c in n["children"]: visit(c, ancestors)
            return
        if kind == "branch":
            visit(n["yes"] if _eval(n["test"], state) else n["no"], ancestors)
            return
        if kind != "element":
            raise ValueError("render node is malformed")
        props = {k: _eval(v, state) for k, v in n["props"].items()}
        if _hidden(props):
            return
        role = _role(n["tag"], props)
        children = n["children"]
        text = "".join(_tree_text(c, state) for c in children)
        name = _display(props.get("aria-label", text or props.get("title", "")))
        handlers = [n["events"]["click"], *reversed(ancestors)] if n["events"].get("click") is not None else list(reversed(ancestors))
        disabled = n["tag"] == "button" and bool(props.get("disabled", False))
        if n["events"].get("click") is not None and not disabled:
            action_role = role if role != "generic" else "clickable"
            label = f"click {action_role} {json.dumps(name, ensure_ascii=False)}" if name else f"click {action_role}"
            out.append({"handler": ["event", *handlers], "label": label, "line": n["line"]})
        for c in children: visit(c, ancestors if disabled else handlers)
    visit(tree, [])
    return out


def _display(value: Any) -> str:
    if value is None:
        return ""
    if value is True:
        return "true"
    if value is False:
        return "false"
    return str(value).strip()


def _hidden(props: dict[str, Any]) -> bool:
    return bool(props.get("hidden")) or props.get("aria-hidden") is True or props.get("aria-hidden") == "true"


def _role(tag: str, props: dict[str, Any]) -> str:
    role = props.get("role")
    if role is not None:
        if not isinstance(role, str) or role not in ARIA_ROLES:
            raise ValueError(f"role {role!r} is outside the source UI role model")
        return role
    return {
        "button": "button", "main": "main", "nav": "navigation", "aside": "complementary", "article": "article",
        "p": "paragraph", "h1": "heading", "h2": "heading", "h3": "heading", "h4": "heading", "h5": "heading", "h6": "heading",
        "div": "generic", "span": "generic",
    }.get(tag, "generic")


def _tree_text(n: dict[str, Any], state: dict[str, Any]) -> str:
    if n["type"] == "text":
        value = _eval(n["value"], state) if isinstance(n["value"], list) else n["value"]
        return "" if value is None or isinstance(value, bool) else str(value)
    if n["type"] == "empty": return ""
    if n["type"] == "group": return "".join(_tree_text(c, state) for c in n["children"])
    if n["type"] == "branch": return _tree_text(n["yes"] if _eval(n["test"], state) else n["no"], state)
    return "".join(_tree_text(c, state) for c in n["children"])


def _snapshot(render: dict[str, Any], state: dict[str, Any], model: dict[str, Any]) -> Snapshot:
    def build(n: dict[str, Any]) -> list[Node]:
        kind = n["type"]
        if kind == "empty": return []
        if kind == "text": return []
        if kind == "group": return [x for c in n["children"] for x in build(c)]
        if kind == "branch": return build(n["yes"] if _eval(n["test"], state) else n["no"])
        props = {k: _eval(v, state) for k, v in n["props"].items()}
        if _hidden(props): return []
        role = _role(n["tag"], props)
        text = "".join(_tree_text(c, state) for c in n["children"])
        name = _display(props.get("aria-label", text or props.get("title", "")))
        states = set()
        if (n["tag"] == "button" and bool(props.get("disabled", False))) or props.get("aria-disabled") is True or props.get("aria-disabled") == "true": states.add("disabled")
        if props.get("checked") or props.get("aria-checked") is True or props.get("aria-checked") == "true": states.add("checked")
        if props.get("aria-checked") == "mixed": states.add("mixed")
        if props.get("aria-expanded") is True or props.get("aria-expanded") == "true": states.add("expanded")
        if props.get("aria-pressed") is True or props.get("aria-pressed") == "true": states.add("pressed")
        if props.get("aria-selected") is True or props.get("aria-selected") == "true": states.add("selected")
        children = [x for c in n["children"] for x in build(c)]
        ref = f"{model['path']}:{n['line']}"
        return [Node(role, name, str(props.get("value")) if "value" in props else None, frozenset(states), ref, props.get("href"), role == "generic" and "click" in n["events"], children=children)]
    return Snapshot("home", Node("generic", children=[x for x in build(render)]), hidden={k: [v] for k, v in state.items()})
