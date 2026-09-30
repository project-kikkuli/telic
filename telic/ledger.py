"""The committed ledger and the CI ratchet.

`telic.ledger.json` records, for every aim, function and mirror, the status
telic established and the contract clauses an aim rests on. It is committed
next to the code, so review sees evidence change like any other diff.

`telic ci` re-checks what a change can affect and compares against the ledger:

* anything that got worse (an aim proved -> open, a function proved ->
  refuted, a mirror that stopped holding) fails the build;
* a contract clause dropped from an aim, or an aim removed, fails too:
  weakening a promise is a decision, not a side effect;
* each such regression can be accepted, one id at a time, with a
  `Telic-accept: <id> <reason>` line in a commit message of the change, which
  review then judges;
* improvements pass, and `--update` (or the pre-push hook) writes them in.

Because it only ratchets, telic can be adopted on a codebase with known
failures: snapshot today's state, and from then on nothing may get worse.

What a change can affect is computed exactly: calls resolve within a module
so the affected files are the changed ones, the files importing them
(transitively), what the TypeScript files among them import, the files
defining the bases of changed classes (a call through a base may run an
override) and their importers, mirror partners, and the files sharing an
aim with them.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .checker import Report, check, language_of
from .contracts import AIM_ID

LEDGER = "telic.ledger.json"
RANK = {"proved": 4, "backed": 4, "trusted": 3, "open": 2, "partial": 2, "unsupported": 2, "error": 1, "vacuous": 1, "unbacked": 1, "unformalized": 1, "undeclared": 1, "refuted": 0, "broken": 0}


# ---------------------------------------------------------------------------
# Building and reading


def snapshot(rep: Report) -> dict[str, Any]:
    aims: dict[str, Any] = {}
    by_key = {f.ref.key: f for f in rep.functions}
    for i in rep.aims:
        clauses = [f"ui {x.name}: {x.text}" for x in i.lemmas if x.kind == "ui"]
        for key in i.functions:
            f = by_key[key]
            for c in f.fn.ensures + f.fn.raises:
                if i.id in c.aims:
                    clauses.append(f"{f.fn.name}: {c.kind} {c.text}")
        aims[i.id] = {
            "status": i.status,
            "text": i.text,
            "functions": sorted(i.functions),
            "clauses": sorted(set(clauses)),
            **({"links": sorted(i.pointers)} if i.pointers else {}),
            **({"declared": i.loc[0]} if i.loc else {}),
        }
    functions = {}
    for f in rep.functions:
        lean = sum(1 for v in f.verdicts if v.method.startswith("lean") or v.reason.startswith("lean"))
        functions[f.ref.key] = {"status": f.status, "obligations": len(f.verdicts), **({"lean": lean} if lean else {})}
    mirrors = {f"{m.a.key} ~ {m.b.key}": m.status for m in rep.mirrors}
    ui = {f"{r.lemma.path}::{r.lemma.name}": r.status for r in rep.ui.results} if rep.ui is not None else {}
    from . import __version__

    return {"telic": __version__, "aims": aims, "functions": functions, "mirrors": mirrors, **({"ui": ui} if ui else {})}


def write_ledger(path: str, data: dict[str, Any]) -> None:
    Path(path).write_text(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + "\n")


def read_ledger(path: str) -> dict[str, Any] | None:
    if not os.path.exists(path):
        return None
    return json.loads(Path(path).read_text())


def merge(old: dict[str, Any], new: dict[str, Any], files: set[str] | None) -> dict[str, Any]:
    """Entries for files outside the checked scope are carried over."""
    if files is None or old is None:
        return new
    out = {"telic": new["telic"], "aims": {}, "functions": {}, "mirrors": {}, "ui": {}}

    def in_scope(key: str) -> bool:
        return key.split("::")[0] in files

    for k, v in old.get("functions", {}).items():
        if not in_scope(k):
            out["functions"][k] = v
    out["functions"].update(new["functions"])
    for k, v in old.get("mirrors", {}).items():
        if not any(in_scope(part.strip()) for part in k.split(" ~ ")):
            out["mirrors"][k] = v
    out["mirrors"].update(new["mirrors"])
    for k, v in old.get("ui", {}).items():
        if not in_scope(k):
            out["ui"][k] = v
    out["ui"].update(new.get("ui", {}))
    if not out["ui"]:
        del out["ui"]
    for k, v in old.get("aims", {}).items():
        if not any(in_scope(f) for f in v.get("functions", []) + [v.get("declared", "")]) and k not in new["aims"]:
            out["aims"][k] = v
    out["aims"].update(new["aims"])
    return out


# ---------------------------------------------------------------------------
# Comparing


@dataclass
class Change:
    id: str
    kind: str  # regression | improvement | new | removed
    what: str
    file: str | None = None


def compare(old: dict[str, Any], new: dict[str, Any], files: set[str] | None) -> list[Change]:
    out: list[Change] = []

    def scoped(key: str) -> bool:
        return files is None or key.split("::")[0] in files

    for iid, o in old.get("aims", {}).items():
        n = new["aims"].get(iid)
        if n is None:
            if files is None or any(scoped(f) for f in o.get("functions", []) + [o.get("declared", "")]):
                out.append(Change(iid, "regression", f"aim {iid} was removed (it was {o['status']})"))
            continue
        if RANK.get(n["status"], 0) < RANK.get(o["status"], 0):
            out.append(Change(iid, "regression", f"aim {iid}: {o['status']} → {n['status']}"))
        elif RANK.get(n["status"], 0) > RANK.get(o["status"], 0):
            out.append(Change(iid, "improvement", f"aim {iid}: {o['status']} → {n['status']}"))
        dropped = sorted(set(o.get("clauses", [])) - set(n.get("clauses", [])))
        for c in dropped:
            out.append(Change(iid, "regression", f"aim {iid} lost a clause: {c}"))
    for iid, n in new["aims"].items():
        if iid not in old.get("aims", {}):
            out.append(Change(iid, "new", f"aim {iid} ({n['status']})"))
    for key, o in old.get("functions", {}).items():
        if not scoped(key):
            continue
        n = new["functions"].get(key)
        if n is None:
            out.append(Change(key, "removed", f"{key} no longer exists", key.split("::")[0]))
            continue
        if RANK.get(n["status"], 0) < RANK.get(o["status"], 0):
            out.append(Change(key, "regression", f"{key}: {o['status']} → {n['status']}", key.split("::")[0]))
        elif RANK.get(n["status"], 0) > RANK.get(o["status"], 0):
            out.append(Change(key, "improvement", f"{key}: {o['status']} → {n['status']}", key.split("::")[0]))
    for key, n in new["functions"].items():
        if key not in old.get("functions", {}):
            kind = "regression" if n["status"] in ("refuted", "error") else "new"
            out.append(Change(key, kind, f"{key} is new ({n['status']})", key.split("::")[0]))
    for key, o in old.get("mirrors", {}).items():
        n = new["mirrors"].get(key)
        if n is None:
            if files is None or any(scoped(p.strip()) for p in key.split(" ~ ")):
                out.append(Change(key, "regression", f"mirror {key} was removed (it was {o})"))
        elif RANK.get(n, 0) < RANK.get(o, 0):
            out.append(Change(key, "regression", f"mirror {key}: {o} → {n}"))
    for key, n in new["mirrors"].items():
        if key not in old.get("mirrors", {}) and n == "refuted":
            out.append(Change(key, "regression", f"mirror {key} is new and diverges"))
    for key, o in old.get("ui", {}).items():
        if not scoped(key):
            continue
        n = new.get("ui", {}).get(key)
        path = key.split("::")[0]
        if n is None:
            out.append(Change(key, "regression", f"ui lemma {key} was removed (it was {o})", path))
        elif RANK.get(n, 0) < RANK.get(o, 0):
            out.append(Change(key, "regression", f"ui {key}: {o} → {n}", path))
        elif RANK.get(n, 0) > RANK.get(o, 0):
            out.append(Change(key, "improvement", f"ui {key}: {o} → {n}", path))
    for key, n in new.get("ui", {}).items():
        if key not in old.get("ui", {}):
            out.append(Change(key, "regression" if n == "refuted" else "new", f"ui {key} is new ({n})", key.split("::")[0]))
    return out


# ---------------------------------------------------------------------------
# Git


def git(root: str, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, check=True).stdout


def changed_files(root: str, base: str) -> set[str]:
    out = git(root, "diff", "--name-only", "--no-renames", f"{base}...HEAD") + git(root, "diff", "--name-only", "--no-renames", "HEAD") + git(root, "ls-files", "--others", "--exclude-standard")
    return {l.strip() for l in out.splitlines() if l.strip()}


def acceptances(root: str, base: str | None) -> dict[str, str]:
    """`Telic-accept: <id> <reason>` lines in the change's commit messages."""
    text = os.environ.get("TELIC_ACCEPT", "")
    if base:
        try:
            text += "\n" + git(root, "log", "--format=%B", f"{base}..HEAD")
        except subprocess.CalledProcessError:
            pass
    out = {}
    for m in re.finditer(r"^Telic-accept:\s*(\S+)\s+(.+)$", text, re.M):
        out[m.group(1)] = m.group(2).strip()
    return out


def affected_files(root: str, changed: set[str], ledger: dict[str, Any] | None) -> set[str]:
    """Changed checkable files, the files that import them (their proofs use
    the changed contracts), their @mirrors partners, and files that share an
    aim with them. A changed subclass also affects the files defining its
    ancestors and their importers: a call through a base may run any
    override. Importers are affected transitively: a proof may unfold a pure
    callee's body, and that body may call into the changed file."""
    from .frontend.aim_file import aim_entry, is_aim_file, lower_aim_entry
    from .aim import _match, split_by

    changed = {aim_entry(f) or f for f in changed}
    files = {f for f in changed if (language_of(f) or is_aim_file(f)) and os.path.exists(os.path.join(root, f))}
    deleted = {f for f in changed if (language_of(f) or is_aim_file(f)) and not os.path.exists(os.path.join(root, f))}
    files |= ui_lemma_files(root, changed)
    # an edited aim file affects the code backing its aims, before and after, and the code its by: names
    md = {f for f in files | deleted if is_aim_file(f)}
    decls = [d for f in md & files for d in lower_aim_entry(f, os.path.join(root, f)).aims]
    ids = {d.id for d in decls}
    known = (ledger or {}).get("functions", {})
    for item in {item for d in decls for item in split_by(d.text)[1]}:
        files |= {k.split("::")[0] for k in known if _match(item, k, k.split("::", 1)[1]) and os.path.exists(os.path.join(root, k.split("::")[0]))}
    ids |= {k for k, v in (ledger or {}).get("aims", {}).items() if v.get("declared") in md}
    for k in ids:
        for key in (ledger or {}).get("aims", {}).get(k, {}).get("functions", []):
            p = key.split("::")[0]
            if os.path.exists(os.path.join(root, p)):
                files.add(p)
    if any(language_of(f) in ("python", "typescript") for f in files | deleted):
        from .frontend.python import ancestor_files
        from .frontend.python import project_imports as py_imports
        from .frontend.typescript import project_imports as ts_imports

        touched = {os.path.normpath(os.path.join(root, f)) for f in files | deleted if language_of(f) in ("python", "typescript")}
        for f in [f for f in files if f.endswith(".py")]:
            for a in ancestor_files(os.path.join(root, f), root):
                touched.add(os.path.normpath(a))
        imports: dict[str, set[str]] = {}
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if not d.startswith(".") and d not in ("node_modules", "__pycache__", "venv", ".venv", "dist", "build")]
            for fn in filenames:
                full = os.path.normpath(os.path.join(dirpath, fn))
                lang = language_of(fn)
                if lang in ("python", "typescript"):
                    imports[full] = {os.path.normpath(x) for x in (py_imports if lang == "python" else ts_imports)(full, root)}
        # A proof may unfold a pure callee's body, which may call further
        # modules, so importers are affected transitively.
        todo = list(touched)
        while todo:
            cur = todo.pop()
            for f, deps in imports.items():
                if cur in deps and f not in touched:
                    touched.add(f)
                    todo.append(f)
        # TypeScript resolves calls only among the files of a run: bring what they import.
        todo = [f for f in touched if language_of(f) == "typescript"]
        while todo:
            for dep in imports.get(todo.pop(), ()):
                if dep not in touched:
                    touched.add(dep)
                    todo.append(dep)
        files |= {os.path.relpath(f, root) for f in touched if os.path.exists(f)}
    grow = True
    named: set[str] = set()  # aim ids the affected code declares or cites
    while grow:
        grow = False
        # mirror partners, both directions (from source and from the ledger)
        for f in list(files):
            if is_aim_file(f):
                continue
            for line in Path(root, f).read_text().splitlines():
                t = line.strip()
                if t.startswith(("#@", "//@")):
                    named.update(re.findall(rf"\baim\s+({AIM_ID})", t))
                if t.startswith(("#@", "//@")) and " mirrors " in t + " " and "::" in t:
                    rel = t.split("mirrors", 1)[1].strip().rsplit("::", 1)[0]
                    tgt = os.path.normpath(os.path.join(os.path.dirname(f), rel))
                    if tgt not in files and os.path.exists(os.path.join(root, tgt)):
                        files.add(tgt)
                        grow = True
        if ledger:
            for key in ledger.get("mirrors", {}):
                parts = [p.strip().split("::")[0] for p in key.split(" ~ ")]
                if any(p in files or p in deleted for p in parts):
                    for p in parts:
                        if p not in files and os.path.exists(os.path.join(root, p)):
                            files.add(p)
                            grow = True
            for iid, v in ledger.get("aims", {}).items():
                fs = {k.split("::")[0] for k in v.get("functions", [])} | ({v["declared"]} if v.get("declared") else set())
                if fs & (files | deleted) or iid in named:
                    for p in fs:
                        if p not in files and os.path.exists(os.path.join(root, p)):
                            files.add(p)
                            grow = True
    return files | deleted


def ui_lemma_files(root: str, changed: set[str]) -> set[str]:
    """A change anywhere in an app with a [ui] section can change how it
    behaves: every file there declaring a ui lemma is affected."""
    from .ui.config import find
    from .ui.spec import scan

    apps = {os.path.dirname(c) for f in changed if os.path.exists(os.path.join(root, f)) and (c := find(os.path.join(root, f), root))}
    return {lem.path for d in apps for lem in scan([d], root).lemmas}


# ---------------------------------------------------------------------------
# Commands


def _paths_and_scope(args, root: str, ledger: dict[str, Any] | None) -> tuple[list[str], set[str] | None]:
    if getattr(args, "since", None):
        scope = affected_files(root, changed_files(root, args.since), ledger)
        live = sorted(f for f in scope if os.path.exists(os.path.join(root, f)))
        return [os.path.join(root, f) for f in live], scope
    return args.paths, None


def cmd_ledger(args) -> int:
    root = os.path.abspath(args.root or os.getcwd())
    path = os.path.join(root, LEDGER)
    old = read_ledger(path)
    paths, scope = _paths_and_scope(args, root, old)
    rep = check(paths, args._options(args, root), root=root) if paths else None
    new = snapshot(rep) if rep else {"telic": "", "aims": {}, "functions": {}, "mirrors": {}}
    data = merge(old, new, scope) if old else new
    write_ledger(path, data)
    n = len(data["functions"])
    ui = f", {len(data['ui'])} ui lemmas" if data.get("ui") else ""
    print(f"wrote {LEDGER}: {len(data['aims'])} aims, {n} functions, {len(data['mirrors'])} mirrors{ui}")
    return 0


def cmd_ci(args) -> int:
    from .render import Paint, Renderer

    root = os.path.abspath(args.root or os.getcwd())
    path = os.path.join(root, LEDGER)
    old = read_ledger(path)
    paths, scope = _paths_and_scope(args, root, old)
    p = Paint(True if args.color == "always" else False if args.color == "never" else None)
    if scope is not None and not paths:
        print(f"{p.bold('telic ci')}  {p.dim('no checkable files changed since ' + args.since)}")
        return 0
    rep = check(paths, args._options(args, root), root=root)
    new = snapshot(rep)
    baseline = old or {"aims": {}, "functions": {}, "mirrors": {}}
    changes = compare(baseline, new, scope)
    accepted = acceptances(root, args.since)
    regressions = [c for c in changes if c.kind == "regression"]
    unaccepted = [c for c in regressions if c.id not in accepted]
    # The full report for anything that is not fine.
    if any(f.status in ("refuted", "vacuous", "open", "error") for f in rep.functions) or any(m.status != "proved" for m in rep.mirrors) or (rep.ui is not None and any(r.status != "proved" for r in rep.ui.results)):
        print(Renderer(rep, p).render())
        print()
    scope_txt = f"{len(paths)} affected file{'s' * (len(paths) != 1)} (since {args.since})" if scope is not None else f"{len(rep.modules)} files"
    print(f"{p.bold('telic ci')}  {p.dim(scope_txt + f' · {rep.cache_hits} reused · {rep.solved} solved · {rep.seconds:.1f}s')}")
    if old is None:
        print(p.yellow(f"  no {LEDGER} yet: every result is new (run 'telic ledger' and commit it)"))
    for c in changes:
        if c.kind == "regression":
            if c.id in accepted:
                print(f"  {p.blue('◇')} {c.what}  {p.dim('accepted: ' + accepted[c.id])}")
            else:
                print(f"  {p.red('✗')} {c.what}")
        elif c.kind == "improvement":
            print(f"  {p.green('↑')} {c.what}")
        elif c.kind == "new":
            print(f"  {p.green('+')} {c.what}")
        else:
            print(f"  {p.dim('−')} {c.what}")
    from .aim import link_problems

    links = link_problems(rep)
    for what, _ in links:
        print(f"  {p.red('✗')} {what}")
    if args.format == "github":
        for what, f in links:
            print(f"::error file={f},title=telic aim link::{what}")
        for c in unaccepted:
            f = c.file or ""
            print(f"::error file={f},title=telic regression::{c.what} (accept with a 'Telic-accept: {c.id} <reason>' commit line)")
        for fr in rep.functions:
            for v in fr.verdicts:
                if v.status == "refuted":
                    line = (v.ob.site or v.ob.loc).line
                    print(f"::error file={fr.ref.module.path},line={line},title=telic: {v.ob.kind} refuted::{v.ob.message}")
        for r in rep.ui.results if rep.ui is not None else []:
            if r.status == "refuted":
                print(f"::error file={r.lemma.path},line={r.lemma.line},title=telic: ui {r.lemma.name} refuted::{r.detail}")
    stale = any(c.kind in ("improvement", "new", "removed") for c in changes) or bool(regressions)
    if args.update and not unaccepted and not links:
        write_ledger(path, merge(old or {}, new, scope) if old else new)
        print(p.dim(f"  updated {LEDGER}"))
    elif stale and not unaccepted and not links:
        print(p.dim(f"  {LEDGER} is behind; 'telic ci --update' (or the pre-push hook) records this"))
    if unaccepted or links:
        print()
        if unaccepted:
            print(p.bred(f"{len(unaccepted)} regression{'s' * (len(unaccepted) != 1)}") + p.dim("  (accept one with a 'Telic-accept: <id> <reason>' line in a commit message)"))
        if links:
            print(p.bred(f"{len(links)} aim link problem{'s' * (len(links) != 1)}") + p.dim("  (fix the declaration or the code; these cannot be accepted)"))
        return 1
    print(p.bgreen("no regressions"))
    return 0


WORKFLOW = """name: telic

on:
  pull_request:
  push:
    branches: [main]

jobs:
  telic:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
      - uses: actions/setup-python@v5
        with:
          python-version: "3.11"
      - uses: actions/setup-node@v4
        with:
          node-version: "22"
      # Receipts are keyed by exact inputs (formula + verifier version), so a
      # branch's cache falls back to main's without any risk of reuse errors.
      # Only main writes the shared cache: pull requests restore but never save.
      - uses: actions/cache/restore@v4
        with:
          path: .telic
          key: telic-${{ github.ref_name }}-${{ github.sha }}
          restore-keys: |
            telic-${{ github.ref_name }}-
            telic-main-
      - run: pip install git+https://github.com/project-kikkuli/telic
      - name: Check what this change can affect against the ledger
        if: github.event_name == 'pull_request'
        run: telic ci --since origin/${{ github.base_ref }} --format github --color always
      - name: Check everything on main
        if: github.event_name == 'push'
        run: telic ci --format github --color always
      - uses: actions/cache/save@v4
        if: github.event_name == 'push' && github.ref == 'refs/heads/main'
        with:
          path: .telic
          key: telic-main-${{ github.sha }}
"""

HOOK = """#!/bin/sh
# telic pre-push hook: check what this push can affect, keep the ledger current.
# Catching a regression here costs seconds; catching it in CI costs a round trip.
base=$(git merge-base HEAD origin/main 2>/dev/null || echo HEAD~1)
exec telic ci --since "$base" --update
"""


def cmd_init(args) -> int:
    root = os.path.abspath(args.root or os.getcwd())
    wf = Path(root, ".github", "workflows", "telic.yml")
    wf.parent.mkdir(parents=True, exist_ok=True)
    made = []
    if not wf.exists():
        wf.write_text(WORKFLOW)
        made.append(str(wf.relative_to(root)))
    gi = Path(root, ".gitignore")
    lines = gi.read_text().splitlines() if gi.exists() else []
    if ".telic/" not in lines:
        gi.write_text("\n".join(lines + [".telic/"]) + "\n")
        made.append(".gitignore (.telic/)")
    hooks = Path(root, ".git", "hooks")
    if hooks.is_dir() and not args.no_hook:
        h = hooks / "pre-push"
        if not h.exists():
            h.write_text(HOOK)
            h.chmod(0o755)
            made.append(".git/hooks/pre-push")
    if not Path(root, LEDGER).exists():
        args.since = None
        args.paths = args.paths or ["."]
        cmd_ledger(args)
        made.append(LEDGER)
    for m in made:
        print(f"  + {m}")
    print("telic is set up: commit telic.ledger.json and .github/workflows/telic.yml")
    return 0


def add_commands(sub, common, options) -> None:
    c = sub.add_parser("ci", help="check what a change can affect and fail on regressions against telic.ledger.json")
    common(c)
    c.add_argument("--since", metavar="REF", help="only files a change since REF can affect (e.g. origin/main)")
    c.add_argument("--update", action="store_true", help="write the new results into the ledger when nothing regressed")
    c.add_argument("--format", choices=["text", "github"], default="text", help="'github' adds workflow annotations")
    c.add_argument("--color", choices=["auto", "always", "never"], default="auto")
    c.set_defaults(func=cmd_ci, _options=options)

    l = sub.add_parser("ledger", help="write telic.ledger.json from a full (or --since) check")
    common(l)
    l.add_argument("--since", metavar="REF")
    l.set_defaults(func=cmd_ledger, _options=options)

    i = sub.add_parser("init", help="set up telic in a repository: ledger, CI workflow, pre-push hook")
    common(i)
    i.add_argument("--no-hook", action="store_true")
    i.set_defaults(func=cmd_init, _options=options)
