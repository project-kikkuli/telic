"""Source-connected finite UI models for a conservative React subset."""

from __future__ import annotations

import hashlib
import html as html_lib
import json
import os
import re
import shlex
import subprocess
from collections import deque
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path
from typing import Any
from urllib.parse import unquote, urlsplit

from ..frontend import typescript
from . import source
from .spec import Pred, Prop, Target, UiLemma
from .tree import Node, Snapshot

EXTRACTOR = Path(__file__).resolve().parent.parent / "frontend" / "ts" / "uistatic.mjs"
MAX_STATES = 4096
ARIA_ROLES = {"alert", "alertdialog", "application", "article", "banner", "blockquote", "button", "caption", "cell", "checkbox", "code", "columnheader", "combobox", "complementary", "contentinfo", "definition", "deletion", "dialog", "document", "emphasis", "feed", "figure", "form", "generic", "grid", "gridcell", "group", "heading", "img", "insertion", "link", "list", "listbox", "listitem", "log", "main", "mark", "marquee", "math", "menu", "menubar", "menuitem", "menuitemcheckbox", "menuitemradio", "meter", "navigation", "note", "option", "paragraph", "progressbar", "radio", "radiogroup", "region", "row", "rowgroup", "rowheader", "scrollbar", "search", "searchbox", "separator", "slider", "spinbutton", "status", "strong", "subscript", "superscript", "switch", "tab", "table", "tablist", "tabpanel", "term", "textbox", "timer", "toolbar", "tooltip", "tree", "treegrid", "treeitem"}


def _vite_react_inputs(top: str) -> tuple[bool, list[str], str | None]:
    package_path = os.path.join(top, "package.json")
    lock_path = os.path.join(top, "package-lock.json")
    tsconfig_path = os.path.join(top, "tsconfig.json")
    configs = [os.path.join(top, f"vite.config.{ext}") for ext in ("js", "mjs", "ts") if os.path.isfile(os.path.join(top, f"vite.config.{ext}"))]
    if not os.path.isfile(package_path) or not os.path.isfile(lock_path) or not os.path.isfile(tsconfig_path) or len(configs) != 1:
        return False, [], "source proof needs a locked Vite React project and one Vite config"
    try:
        package = json.loads(Path(package_path).read_text())
        lock = json.loads(Path(lock_path).read_text())
        config = Path(configs[0]).read_text()
        tsconfig = json.loads(Path(tsconfig_path).read_text())
        installed = {}
        for name in ("vite", "@vitejs/plugin-react", "react", "react-dom"):
            installed_path = os.path.join(top, "node_modules", *name.split("/"), "package.json")
            installed[name] = json.loads(Path(installed_path).read_text())
    except (OSError, ValueError, KeyError) as e:
        return False, [], f"cannot establish the installed Vite React toolchain: {e}"
    expected = "import{defineConfig}from'vite'importreactfrom'@vitejs/plugin-react'exportdefaultdefineConfig({plugins:[react()]})"
    compact = re.sub(r",([}\]])", r"\1", re.sub(r"\s+", "", re.sub(r"//[^\n]*|/\*[\s\S]*?\*/", "", config))).rstrip(";")
    deps = {**package.get("dependencies", {}), **package.get("devDependencies", {})}
    locked = lock.get("packages", {})
    required = ("vite", "@vitejs/plugin-react", "react", "react-dom")
    lock_root = locked.get("", {})
    bin_path = os.path.join(top, "node_modules", ".bin", "vite")
    vite_bin = installed["vite"].get("bin", {}).get("vite")
    compiler = tsconfig.get("compilerOptions", {})
    unsupported_configs = (".babelrc", ".babelrc.json", ".babelrc.js", ".babelrc.cjs", "babel.config.js", "babel.config.cjs", "babel.config.mjs", ".swcrc")
    if compact != expected or tsconfig.get("extends") or compiler.get("jsx") != "react-jsx" or any(k in compiler for k in ("jsxImportSource", "jsxFactory", "jsxFragmentFactory", "plugins")):
        return False, [], "Vite React JSX compilation options are outside the verified pipeline"
    if any(os.path.isfile(os.path.join(top, f)) for f in unsupported_configs):
        return False, [], "custom Babel or SWC transforms are outside the verified Vite pipeline"
    if any(name not in deps or lock_root.get("dependencies", {}).get(name) != deps[name] and lock_root.get("devDependencies", {}).get(name) != deps[name]
           or locked.get(f"node_modules/{name}", {}).get("version") != installed[name].get("version") for name in required):
        return False, [], "Vite config, package lock, or installed React toolchain is outside the verified pipeline"
    if not vite_bin or not os.path.isfile(bin_path) or os.path.realpath(bin_path) != os.path.realpath(os.path.join(top, "node_modules", "vite", vite_bin)):
        return False, [], "Vite config, package lock, or installed React toolchain is outside the verified pipeline"
    return True, [package_path, lock_path, configs[0], tsconfig_path, *(os.path.join(top, "node_modules", *name.split("/"), "package.json") for name in required), bin_path], None


def _css_model(texts: list[str]) -> tuple[list[dict[str, Any]], bool]:
    rules: list[dict[str, Any]] = []
    layout_sensitive = False
    for text in texts:
        text = re.sub(r"/\*[\s\S]*?\*/", "", text)
        depth = 0
        for char in text:
            if char == "@":
                raise ValueError("CSS at-rules need viewport-specific layout modeling")
            if char == "{":
                depth += 1
                if depth > 1:
                    raise ValueError("nested CSS rules need viewport-specific layout modeling")
            elif char == "}":
                depth -= 1
                if depth < 0:
                    raise ValueError("CSS rule boundaries cannot be parsed")
        if depth:
            raise ValueError("CSS rule boundaries cannot be parsed")
        for selector_text, body in re.findall(r"([^{}]+)\{([^{}]*)\}", text):
            declarations: dict[str, str] = {}
            for declaration in body.split(";"):
                if not declaration.strip():
                    continue
                if ":" not in declaration:
                    raise ValueError("a CSS declaration cannot be parsed")
                key, value = declaration.split(":", 1)
                if "!important" in value.lower():
                    raise ValueError("CSS !important declarations need full cascade modeling")
                declarations[key.strip().lower()] = value.strip().lower()
            if declarations.get("display") is not None and declarations["display"] != "none":
                layout_sensitive = True
            if declarations.get("visibility") not in (None, "visible", "hidden", "collapse"):
                raise ValueError("CSS visibility value is outside the source style model")
            if any(k not in {"display", "visibility", "color", "background", "background-color", "text-decoration", "border-color"} for k in declarations):
                layout_sensitive = True
            if not {"display", "visibility"}.intersection(declarations):
                continue
            for selector in selector_text.split(","):
                selector = selector.strip()
                m = re.fullmatch(r"(?:(?P<tag>[a-z][a-z0-9-]*))?(?P<classes>(?:\.[_a-zA-Z][\w-]*)*)", selector)
                if not m or not (m.group("tag") or m.group("classes")):
                    raise ValueError(f"CSS visibility selector {selector!r} is outside the source style model")
                classes = [c for c in m.group("classes").split(".") if c]
                rules.append({"tag": m.group("tag"), "classes": classes, "specificity": [len(classes), int(bool(m.group("tag")))], "display": declarations.get("display"), "visibility": declarations.get("visibility")})
    return rules, layout_sensitive


@dataclass
class StaticOutcome:
    status: str
    method: str
    detail: str
    trace: list[str] | None = None
    source: list[str] | None = None
    receipt: dict[str, Any] | None = None


def extract(top: str, root: str, html_entry: str = "index.html", pipeline: str | None = None, *, config_path: str | None = None, command: str | None = None, config_digest: str | None = None) -> tuple[dict[str, Any] | None, str | None, str | None]:
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
    if css and pipeline != "vite-react":
        return None, None, f"CSS can change the accessibility tree ({os.path.relpath(css[0], root)}); layout/style semantics are not modeled"
    entries = []
    css_texts: list[str] = []
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
    if pipeline == "vite-react":
        if not config_path or not command or not config_digest:
            return None, None, "source proof needs the configured Vite command and UI configuration"
        try:
            config_bytes = Path(config_path).read_bytes()
            import tomllib
            ui = tomllib.loads(config_bytes.decode("utf-8")).get("ui", {})
        except OSError as e:
            return None, None, f"cannot read UI configuration: {e}"
        except (UnicodeDecodeError, ValueError) as e:
            return None, None, f"cannot parse UI configuration: {e}"
        try:
            args = tuple(shlex.split(command))
        except ValueError:
            args = ()
        allowed = {
            ("npx", "vite", "--port", "{port}"),
            ("npx", "vite", "--port", "{port}", "--strictPort"),
            ("npx", "vite", "--port", "{port}", "--strictPort", "--host", "127.0.0.1"),
            ("npx", "vite", "--port", "{port}", "--host", "127.0.0.1"),
        }
        actual_digest = hashlib.sha256(json.dumps(ui, sort_keys=True, default=str).encode()).hexdigest()[:16]
        configured_url = str(ui.get("url") or "")
        parsed_url = urlsplit(configured_url)
        url_matches_server = not configured_url or (
            parsed_url.scheme == "http" and parsed_url.hostname in ("127.0.0.1", "localhost")
            and "{port}" in parsed_url.netloc and parsed_url.path in ("", "/")
            and not parsed_url.query and not parsed_url.fragment and parsed_url.username is None and parsed_url.password is None
        )
        if (ui.get("command") != command or args not in allowed or ui.get("static") or ui.get("build") or ui.get("inputs") is not None
                or actual_digest != config_digest or not url_matches_server):
            return None, None, "source proof is not bound to this configured Vite app, command, URL, and UI inputs"
        verified, tool_inputs, why = _vite_react_inputs(top)
        if not verified:
            return None, None, why
        for full in css:
            try:
                data = Path(full).read_bytes()
                text = data.decode("utf-8")
            except (OSError, UnicodeDecodeError) as e:
                return None, None, f"cannot read app stylesheet {os.path.relpath(full, root)}: {e}"
            rel = os.path.relpath(full, root).replace(os.sep, "/")
            entries.append({"path": rel, "text": text})
            css_texts.append(text)
            dig.update(rel.encode() + b"\0" + data + b"\0")
        entries.extend({"path": os.path.relpath(full, top).replace(os.sep, "/"), "text": Path(full).read_text(encoding="utf-8")} for full in css)
        dig.update(os.path.relpath(config_path, root).replace(os.sep, "/").encode() + b"\0" + config_bytes + b"\0")
        for full in tool_inputs:
            try:
                data = Path(full).read_bytes()
            except OSError as e:
                return None, None, f"cannot read Vite input {os.path.relpath(full, root)}: {e}"
            rel = os.path.relpath(full, root).replace(os.sep, "/")
            dig.update(rel.encode() + b"\0" + data + b"\0")
    html_documents: list[tuple[set[str], set[str], bool, list[tuple[str, str | None, int, set[str]]], bool, set[str], set[str]]] = []
    html_deps = []
    class IdParser(HTMLParser):
        def __init__(self, base_dir: str) -> None:
            super().__init__(convert_charrefs=True)
            self.base_dir = base_dir
            self.ids: set[str] = set()
            self.scripts: set[str] = set()
            self.active_script = False
            self.active_script_inline = False
            self.invalid_script = False
            self.invalid_markup = False
            self.in_body = False
            self.body_attrs: set[str] = set()
            self.html_attrs: set[str] = set()
            self.seen_body = False
            self.body_elements: list[tuple[str, str | None, int, set[str]]] = []
            self.stack: list[str] = []

        def handle_starttag(self, _tag: str, attrs: list[tuple[str, str | None]]) -> None:
            values = dict(attrs)
            if _tag == "html":
                self.html_attrs = set(values)
            if _tag == "base" or _tag == "meta" and (values.get("http-equiv") or "").lower() in ("refresh", "content-security-policy", "content-security-policy-report-only"):
                self.invalid_markup = True
            if values.get("id") is not None:
                self.ids.add(values["id"] or "")
            if _tag == "body":
                if self.seen_body:
                    self.invalid_markup = True
                self.seen_body = True
                self.in_body = True
                self.body_attrs = set(values)
                self.stack = ["body"]
                return
            if not self.in_body and _tag not in {"html", "head", "base", "link", "meta", "title", "style", "script", "noscript", "template"}:
                self.invalid_markup = True
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
            executable = kind in ("", "module", "text/javascript", "application/javascript", "text/ecmascript", "application/ecmascript", "application/x-javascript")
            self.active_script_inline = not src and executable
            if kind == "importmap" or "nomodule" in values or "integrity" in values:
                self.invalid_script = True
            if src and executable:
                parsed_src = urlsplit(src)
                if parsed_src.scheme or parsed_src.netloc or parsed_src.query or parsed_src.fragment:
                    self.scripts.add("external:" + src)
                else:
                    path = unquote(parsed_src.path)
                    base = "" if path.startswith("/") else self.base_dir
                    self.scripts.add(os.path.normpath(os.path.join(base, path.lstrip("/"))))

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
    selected_html = os.path.normpath(os.path.join(top, html_entry))
    if os.path.commonpath((os.path.abspath(top), os.path.abspath(selected_html))) != os.path.abspath(top):
        return None, None, "configured static HTML entry leaves the served directory"
    for full in [selected_html] if os.path.isfile(selected_html) else []:
        try:
            data = Path(full).read_bytes()
            text = data.decode("utf-8")
        except (OSError, UnicodeDecodeError) as e:
            return None, None, f"cannot read app HTML {os.path.relpath(full, root)}: {e}"
        rel = os.path.relpath(full, root).replace(os.sep, "/")
        html_deps.append(rel)
        dig.update(rel.encode() + b"\0" + data + b"\0")
        parser = IdParser(os.path.dirname(os.path.relpath(full, top)))
        parser.feed(text)
        html_documents.append((parser.ids, parser.scripts, parser.invalid_script, parser.body_elements, parser.invalid_markup, parser.body_attrs, parser.html_attrs))
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
    try:
        styles, layout_sensitive = _css_model(css_texts)
    except ValueError as e:
        return None, identity, str(e)
    if any(rule["tag"] in ("html", "body") for rule in styles):
        return None, identity, "HTML or body visibility styles affect the app outside the rendered source tree"
    def decode_jsx(node: Any) -> None:
        if not isinstance(node, dict):
            return
        if node.get("type") == "jsxText":
            node["type"] = "text"
            node["value"] = html_lib.unescape(node["value"])
        if node.get("type") == "text" and isinstance(node.get("value"), list) and node["value"][0] == "jsx-lit":
            node["value"] = ["lit", html_lib.unescape(node["value"][1])]
        if node.get("type") == "element":
            node["props"] = {k: (["lit", html_lib.unescape(v[1])] if isinstance(v, list) and len(v) == 2 and v[0] == "jsx-lit" else v) for k, v in node.get("props", {}).items()}
        for child in node.get("children", []):
            decode_jsx(child)
        for key in ("yes", "no"):
            if key in node:
                decode_jsx(node[key])
        if node.get("type") == "component":
            decode_jsx(node["child"])
    decode_jsx(models[0]["render"])
    root_id, entry = models[0].get("mountRoot"), os.path.normpath(models[0].get("mountEntry", ""))
    entry_served = os.path.normpath(os.path.relpath(os.path.join(root, entry), top))
    def hosts_model(ids: set[str], scripts: set[str], invalid_script: bool, body: list[tuple[str, str | None, int, set[str]]], invalid_markup: bool, body_attrs: set[str], html_attrs: set[str]) -> bool:
        hosts = [x for x in body if x[1] == root_id]
        visible = [x for x in body if x[0] != "script"]
        if invalid_script or invalid_markup or scripts != {entry_served} or len(hosts) != 1 or visible != hosts or not body_attrs <= {"lang", "dir"} or not html_attrs <= {"lang", "dir"}:
            return False
        tag, _, depth, attrs = hosts[0]
        return tag == "div" and depth == 0 and attrs <= {"id"}
    if not any(hosts_model(*document) for document in html_documents):
        return None, identity, f"static app HTML does not connect a #{root_id} root to the mounted entry {entry}"
    if pipeline != "vite-react" and Path(entry).suffix.lower() in (".ts", ".tsx", ".jsx"):
        return None, identity, "a browser cannot execute TypeScript or JSX from a raw static directory"
    models[0]["dependencies"] = sorted([*(e["path"] for e in entries), *html_deps, *([os.path.relpath(p, root).replace(os.sep, "/") for p in tool_inputs] if pipeline == "vite-react" else [])])
    models[0]["pipeline"] = pipeline or "raw-static"
    models[0]["styles"] = styles
    models[0]["layout_sensitive"] = layout_sensitive
    return models[0], identity, None


def check(model: dict[str, Any], identity: str, lem: UiLemma) -> StaticOutcome:
    if lem.prop is None:
        return StaticOutcome("open", "source model", "the UI property could not be parsed")
    if model.get("pipeline") != "vite-react":
        return StaticOutcome("open", "source model", "the source model is not tied to a verified compiler and configured app")
    try:
        states, edges, snaps = _graph(model)
    except ValueError as e:
        return StaticOutcome("open", "source model", str(e))
    prop = lem.prop
    if prop.kind in ("unobscured", "persists"):
        return StaticOutcome("open", "source model", f"{prop.kind} needs {('CSS/layout geometry' if prop.kind == 'unobscured' else 'a storage/reopen model')}; it is not inferred from rendered roles")
    if model.get("layout_sensitive"):
        return StaticOutcome("open", "source model", "CSS layout can change which physical clicks reach their handlers")
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


def _css_style(node: dict[str, Any], props: dict[str, Any], model: dict[str, Any], inherited: str) -> tuple[str | None, str]:
    display = None
    visibility = inherited
    classes = set(str(props.get("className", "")).split())
    tag = node.get("tag", "").lower()
    for rule in sorted(model.get("styles", []), key=lambda r: r["specificity"]):
        if (rule["tag"] is None or rule["tag"] == tag) and set(rule["classes"]) <= classes:
            if rule["display"] is not None:
                display = rule["display"]
            if rule["visibility"] is not None:
                visibility = rule["visibility"]
    return display, visibility


def _graph(model: dict[str, Any]) -> tuple[list[dict[str, Any]], list[list[tuple[int, str]]], list[Snapshot]]:
    declarations = model["states"]
    state_defs = {d["name"]: d for d in declarations}
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
            before_mounts = _mounted_components(model["render"], current)
            after_mounts = _mounted_components(model["render"], nxt)
            for declaration in declarations:
                owner = declaration.get("owner")
                if owner and owner in before_mounts and owner not in after_mounts:
                    nxt[declaration["name"]] = declaration["initial"]
            for name, value in nxt.items():
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


def _truthy(value: Any) -> bool:
    if value is None or value is False:
        return False
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return value != 0
    if isinstance(value, str):
        return bool(value)
    return True


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
    if op == "member":
        obj, key = _eval(e[1], state, locals_), _eval(e[2], state, locals_)
        if isinstance(obj, list):
            if key == "length": return len(obj)
            if isinstance(key, int) and not isinstance(key, bool):
                if 0 <= key < len(obj): return obj[key]
                raise ValueError("JavaScript array access can be out of bounds")
            if isinstance(key, str) and key.isdecimal():
                index = int(key)
                if 0 <= index < len(obj): return obj[index]
                raise ValueError("JavaScript array access can be out of bounds")
            raise ValueError("JavaScript array property is outside the finite UI model")
        if isinstance(obj, str):
            units = obj.encode("utf-16-le", "surrogatepass")
            if key == "length": return len(units) // 2
            if isinstance(key, int) and not isinstance(key, bool) and 0 <= key < len(units) // 2:
                return units[key * 2:key * 2 + 2].decode("utf-16-le", "surrogatepass")
            if isinstance(key, str) and key.isdecimal():
                index = int(key)
                if 0 <= index < len(units) // 2: return units[index * 2:index * 2 + 2].decode("utf-16-le", "surrogatepass")
            raise ValueError("JavaScript string property is outside the finite UI model")
        if isinstance(obj, dict):
            if str(key) in obj: return obj[str(key)]
            raise ValueError("JavaScript object property is not present in the static UI value")
        raise ValueError("JavaScript property access is modeled only for static arrays, objects, and strings")
    if op == "un":
        v = _eval(e[2], state, locals_)
        if e[1] == "not": return not v
        if isinstance(v, bool): v = int(v)
        if not isinstance(v, int):
            raise ValueError("JavaScript unary numeric coercion is outside the source UI model")
        return -v if e[1] == "neg" else v
    if op == "if":
        return _eval(e[2] if _truthy(_eval(e[1], state, locals_)) else e[3], state, locals_)
    if op == "bin":
        a, b = _eval(e[2], state, locals_), _eval(e[3], state, locals_)
        if isinstance(a, (list, dict)) or isinstance(b, (list, dict)):
            raise ValueError("JavaScript object identity is outside the source UI expression model")
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
            "eq": lambda: same, "ne": lambda: not same, "and": lambda: b if _truthy(a) else a, "or": lambda: a if _truthy(a) else b,
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
        branch = stmt[2] if _truthy(_eval(stmt[1], captured)) else stmt[3]
        return _execute(branch, captured, updated, defs)
    if op == "invoke":
        return _execute(stmt[1], captured, updated, defs)
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
    def visit(n: dict[str, Any], ancestors: list[Any] | None = None, parent_display_none: bool = False, inherited_visibility: str = "visible") -> None:
        ancestors = ancestors or []
        if parent_display_none:
            return
        kind = n["type"]
        if kind in ("empty", "text"):
            return
        if kind == "group":
            for c in n["children"]: visit(c, ancestors)
            return
        if kind == "branch":
            visit(n["yes"] if _truthy(_eval(n["test"], state)) else n["no"], ancestors)
            return
        if kind == "component":
            visit(n["child"], ancestors, False, inherited_visibility)
            return
        if kind != "element":
            raise ValueError("render node is malformed")
        props = {k: _eval(v, state) for k, v in n["props"].items()}
        display, visibility = _css_style(n, props, model, inherited_visibility)
        if _dom_hidden(props) or display == "none":
            return
        role = _role(n["tag"], props)
        children = n["children"]
        name = _accessible_name(n, props, state, role, model)
        handlers = [n["events"]["click"], *reversed(ancestors)] if n["events"].get("click") is not None else list(reversed(ancestors))
        disabled = n["tag"] == "button" and bool(props.get("disabled", False))
        if n["events"].get("click") is not None and not disabled and visibility not in ("hidden", "collapse"):
            action_role = role if role != "generic" else "clickable"
            label = f"click {action_role} {json.dumps(name, ensure_ascii=False)}" if name else f"click {action_role}"
            out.append({"handler": ["event", *handlers], "label": label, "line": n["line"]})
        next_ancestors = [*ancestors, n["events"]["click"]] if n["events"].get("click") is not None and not disabled else ancestors
        for c in children: visit(c, next_ancestors, False, visibility)
    visit(tree, [])
    return out


def _mounted_components(tree: dict[str, Any], state: dict[str, Any]) -> set[str]:
    mounted: set[str] = set()
    def visit(node: dict[str, Any]) -> None:
        kind = node["type"]
        if kind == "branch":
            visit(node["yes"] if _truthy(_eval(node["test"], state)) else node["no"])
        elif kind == "group":
            for child in node["children"]: visit(child)
        elif kind == "component":
            mounted.add(node["id"])
            visit(node["child"])
        elif kind == "element":
            for child in node["children"]: visit(child)
    visit(tree)
    return mounted


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


def _dom_hidden(props: dict[str, Any]) -> bool:
    return bool(props.get("hidden"))


def _accessible_name(node: dict[str, Any], props: dict[str, Any], state: dict[str, Any], role: str, model: dict[str, Any]) -> str:
    if role == "generic":
        return ""
    references = _display(props.get("aria-labelledby", ""))
    if references:
        labels = _id_texts(model["render"], state, model)
        if len(set(references.split())) != len(references.split()):
            raise ValueError("aria-labelledby repeats an id outside the source name model")
        return _display(" ".join(labels[x] for x in references.split() if x in labels))
    aria = _display(props.get("aria-label", ""))
    if aria:
        return aria
    text = "".join(_tree_text(c, state, model) for c in node.get("children", []))
    return _display(text or props.get("title", ""))


def _id_texts(tree: dict[str, Any], state: dict[str, Any], model: dict[str, Any]) -> dict[str, str]:
    labels: dict[str, str] = {}
    def raw_text(node: dict[str, Any]) -> str:
        kind = node["type"]
        if kind == "text":
            value = _eval(node["value"], state) if isinstance(node["value"], list) else node["value"]
            if isinstance(value, (list, dict)):
                raise ValueError("React object and array children need explicit child-node modeling")
            return "" if value is None or isinstance(value, bool) else str(value)
        if kind == "jsxText": return html_lib.unescape(node["value"])
        if kind == "empty": return ""
        if kind == "component": return raw_text(node["child"])
        if kind == "group": return "".join(raw_text(c) for c in node["children"])
        if kind == "branch": return raw_text(node["yes"] if _truthy(_eval(node["test"], state)) else node["no"])
        return "".join(raw_text(c) for c in node["children"])
    def visit(node: dict[str, Any]) -> None:
        kind = node["type"]
        if kind == "branch":
            visit(node["yes"] if _truthy(_eval(node["test"], state)) else node["no"])
        elif kind == "group":
            for child in node["children"]: visit(child)
        elif kind == "component":
            visit(node["child"])
        elif kind == "element":
            props = {k: _eval(v, state) for k, v in node["props"].items()}
            key = props.get("id")
            if key:
                if not isinstance(key, str):
                    raise ValueError("non-string ids affect aria-labelledby name resolution")
                if key in labels:
                    raise ValueError("duplicate ids affect aria-labelledby name resolution")
                labels[key] = raw_text({"type": "group", "children": node["children"]})
            for child in node["children"]: visit(child)
    visit(tree)
    return labels


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


def _tree_text(n: dict[str, Any], state: dict[str, Any], model: dict[str, Any], inherited_visibility: str = "visible", inherited_aria_hidden: bool = False) -> str:
    if n["type"] == "text":
        value = _eval(n["value"], state) if isinstance(n["value"], list) else n["value"]
        if isinstance(value, (list, dict)):
            raise ValueError("React object and array children need explicit child-node modeling")
        return "" if value is None or isinstance(value, bool) else str(value)
    if n["type"] == "empty": return ""
    if n["type"] == "jsxText": return html_lib.unescape(n["value"])
    if inherited_aria_hidden: return ""
    if n["type"] == "component": return _tree_text(n["child"], state, model, inherited_visibility, inherited_aria_hidden)
    if n["type"] == "group": return "".join(_tree_text(c, state, model, inherited_visibility, inherited_aria_hidden) for c in n["children"])
    if n["type"] == "branch": return _tree_text(n["yes"] if _truthy(_eval(n["test"], state)) else n["no"], state, model, inherited_visibility, inherited_aria_hidden)
    props = {k: _eval(v, state) for k, v in n.get("props", {}).items()}
    if _dom_hidden(props): return ""
    aria_hidden = props.get("aria-hidden") is True or props.get("aria-hidden") == "true"
    if aria_hidden: return ""
    display, visibility = _css_style(n, props, model, inherited_visibility)
    if display == "none" or visibility in ("hidden", "collapse"): return ""
    return "".join(_tree_text(c, state, model, visibility, inherited_aria_hidden or aria_hidden) for c in n["children"])


def _snapshot(render: dict[str, Any], state: dict[str, Any], model: dict[str, Any]) -> Snapshot:
    def build(n: dict[str, Any], inherited_visibility: str = "visible", inherited_aria_hidden: bool = False) -> list[Node]:
        kind = n["type"]
        if kind == "empty": return []
        if kind == "text": return []
        if kind == "group": return [x for c in n["children"] for x in build(c, inherited_visibility, inherited_aria_hidden)]
        if kind == "branch": return build(n["yes"] if _truthy(_eval(n["test"], state)) else n["no"], inherited_visibility, inherited_aria_hidden)
        if kind == "component": return build(n["child"], inherited_visibility, inherited_aria_hidden)
        props = {k: _eval(v, state) for k, v in n["props"].items()}
        if _dom_hidden(props): return []
        aria_hidden = inherited_aria_hidden or props.get("aria-hidden") is True or props.get("aria-hidden") == "true"
        if aria_hidden: return []
        display, visibility = _css_style(n, props, model, inherited_visibility)
        if display == "none": return []
        role = _role(n["tag"], props)
        name = _accessible_name(n, props, state, role, model)
        states = set()
        if (n["tag"] == "button" and bool(props.get("disabled", False))) or props.get("aria-disabled") is True or props.get("aria-disabled") == "true": states.add("disabled")
        if props.get("checked") or props.get("aria-checked") is True or props.get("aria-checked") == "true": states.add("checked")
        if props.get("aria-checked") == "mixed": states.add("mixed")
        if props.get("aria-expanded") is True or props.get("aria-expanded") == "true": states.add("expanded")
        if props.get("aria-pressed") is True or props.get("aria-pressed") == "true": states.add("pressed")
        if props.get("aria-selected") is True or props.get("aria-selected") == "true": states.add("selected")
        children = [x for c in n["children"] for x in build(c, visibility, aria_hidden)]
        if visibility in ("hidden", "collapse"):
            return children
        ref = f"{model['path']}:{n['line']}"
        return [Node(role, name, str(props.get("value")) if "value" in props else None, frozenset(states), ref, props.get("href"), role == "generic" and "click" in n["events"], children=children)]
    return Snapshot("home", Node("generic", children=[x for x in build(render)]), hidden={k: [v] for k, v in state.items()})
