"""Reuse proof receipts; audit verifier semantics only when their inputs change."""

from __future__ import annotations

import argparse
import ast
import fnmatch
import glob
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
RECEIPTS = ROOT / ".telic" / "ci-verdicts.json"
CI_SETUP = ["scripts/ci.py", ".github/workflows/ci.yml", ".github/constraints.txt", "pyproject.toml"]
TEST_SETUP = CI_SETUP + ["tests/conftest.py"]
PROOF_SETUP = CI_SETUP

_JS_IMPORT = re.compile(r"(?m)^\s*(?:import\s+(?:[^\n]*?\s+from\s*)?|import\s*|export\s+[^\n]*?\s+from\s*)[\"'](\.[^\"']+)[\"']")
_JS_DYNAMIC_IMPORT = re.compile(r"\bimport\s*\(\s*[\"'](\.[^\"']+)[\"']")
_PY_DIRECTIVE = {
    name: re.compile(rf"^\s*#@\s*(?:\[[^]]+\]\s*)?{name}\b", re.M)
    for name in ("mirrors", "ui")
}
_HOST_DIRECTIVE = {
    name: re.compile(rf"^\s*//@\s*(?:\[[^]]+\]\s*)?{name}\b", re.M)
    for name in ("mirrors", "ui")
}


def _python_module(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    parts = rel.parts[:-1] if rel.name == "__init__" else rel.parts
    return ".".join(parts)


def _module_file(module: str) -> Path | None:
    if not module:
        return None
    if module == "telic" or module.startswith("telic.") or module == "tests" or module.startswith("tests."):
        base = ROOT.joinpath(*module.split("."))
    else:
        base = ROOT / "tests" / module
    for candidate in (base.with_suffix(".py"), base / "__init__.py"):
        if candidate.is_file():
            return candidate
    return None


def _local_imports(path: Path) -> set[Path]:
    tree = ast.parse(path.read_text(), filename=str(path))
    package = _python_module(path)
    if path.name != "__init__.py":
        package = package.rpartition(".")[0]
    out: set[Path] = set()
    for node in ast.walk(tree):
        modules: list[str] = []
        if isinstance(node, ast.Import):
            modules.extend(alias.name for alias in node.names if alias.name == "telic" or alias.name.startswith("telic.") or alias.name == "tests" or alias.name.startswith("tests."))
        elif isinstance(node, ast.ImportFrom):
            if node.level:
                parts = package.split(".") if package else []
                if node.level > len(parts) + 1:
                    raise RuntimeError(f"invalid relative import in {path.relative_to(ROOT)}:{node.lineno}")
                base = parts[: len(parts) - node.level + 1]
                if node.module:
                    modules.append(".".join(base + node.module.split(".")))
                else:
                    modules.extend(".".join(base + [alias.name]) for alias in node.names)
            elif node.module and (node.module == "telic" or node.module.startswith("telic.") or node.module == "tests" or node.module.startswith("tests.")):
                modules.append(node.module)
                modules.extend(f"{node.module}.{alias.name}" for alias in node.names)
        for module in modules:
            found = _module_file(module)
            if found is not None:
                out.add(found)
    return out


def python_sources(roots: list[str], excluded: list[str] = ()) -> list[str]:
    """Follow every repository-local Python import from executable roots.

    Language dispatch, UI execution, and prover-agent commands are excluded
    here and added only by the gate paths that actually select them. Imports
    inside functions are included conservatively because the loader dispatches
    through those paths at runtime.
    """
    seen: set[Path] = set()
    todo = [ROOT / root for root in roots]
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        if not path.is_file():
            raise RuntimeError(f"missing CI Python dependency: {path.relative_to(ROOT)}")
        rel = str(path.relative_to(ROOT))
        if any(fnmatch.fnmatch(rel, pattern) for pattern in excluded):
            continue
        seen.add(path)
        todo.extend(_local_imports(path) - seen)
    return sorted(str(path.relative_to(ROOT)) for path in seen)


def javascript_sources(roots: list[str]) -> list[str]:
    """Follow local ES module edges used by the TypeScript lowering/replay workers."""
    seen: set[Path] = set()
    todo = [ROOT / root for root in roots]
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        if not path.is_file():
            raise RuntimeError(f"missing CI JavaScript dependency: {path.relative_to(ROOT)}")
        seen.add(path)
        source = path.read_text()
        imports = _JS_IMPORT.findall(source) + _JS_DYNAMIC_IMPORT.findall(source)
        for spec in imports:
            base = (path.parent / spec).resolve()
            candidates = (base, base.with_suffix(".mjs"), base.with_suffix(".js"), base / "index.mjs")
            dep = next((candidate for candidate in candidates if candidate.is_file() and candidate.is_relative_to(ROOT)), None)
            if dep is None:
                raise RuntimeError(f"unresolved local JavaScript import {spec!r} in {path.relative_to(ROOT)}")
            todo.append(dep)
        if "import(" in source and not _JS_DYNAMIC_IMPORT.search(source):
            todo.extend(ROOT.glob("telic/frontend/ts/**/*.mjs"))
    return sorted(str(path.relative_to(ROOT)) for path in seen)


def has_directive(patterns: list[str], directive: str) -> bool:
    for pattern in patterns:
        for path in ROOT.glob(pattern):
            if not path.is_file():
                continue
            markers = _PY_DIRECTIVE if path.suffix == ".py" else _HOST_DIRECTIVE
            if markers[directive].search(path.read_text(errors="replace")):
                return True
    return False


def verifier_sources(languages: set[str], replay: bool, mirrors: bool, ui: bool, prover: bool = False) -> list[str]:
    roots = ["telic/checker.py", "telic/frontend/python.py"]
    if replay:
        roots.append("telic/replay_harness.py")
    for language in languages - {"python"}:
        if language == "typescript":
            roots.append("telic/frontend/typescript.py")
        elif language == "rust":
            roots.append("telic/frontend/rust.py")
        elif language == "swift":
            roots.append("telic/frontend/swift.py")
    excluded = []
    if not ui:
        excluded.append("telic/ui/run.py")
    if not mirrors:
        excluded.append("telic/equiv.py")
    if not prover:
        excluded.append("telic/prover.py")
    for language in {"typescript", "rust", "swift"} - languages:
        excluded.append({
            "typescript": "telic/frontend/typescript.py",
            "rust": "telic/frontend/rust*.py",
            "swift": "telic/frontend/swift*.py",
        }[language])
    if not replay:
        excluded.extend(["telic/replay.py", "telic/replay_harness.py", "telic/frontend/*_replay.py"])
    return python_sources(roots, excluded)


def telic_python_sources() -> list[str]:
    return sorted(str(path.relative_to(ROOT)) for path in (ROOT / "telic").rglob("*.py") if "demo" not in path.relative_to(ROOT).parts)


def proof_sidecars() -> list[str]:
    return sorted(str(path.relative_to(ROOT)) for path in (ROOT / "telic").rglob("*.proof.lean") if "demo" not in path.relative_to(ROOT).parts)


def test_inputs(patterns: list[str], *, languages: set[str], replay: bool, native: bool = False,
                lean: bool = False, prover: bool = False) -> list[str]:
    fixtures = [pattern for pattern in patterns if pattern.startswith("tests/cases/")]
    mirrors = has_directive(fixtures, "mirrors")
    ui = has_directive(fixtures, "ui")
    test_roots = [pattern for pattern in patterns if pattern.startswith("tests/") and not any(c in pattern for c in "*?[")]
    files = verifier_sources(languages, replay, mirrors, ui, prover) + python_sources(test_roots + ["tests/conftest.py"])
    if "typescript" in languages:
        files += javascript_sources(["telic/frontend/ts/lower.mjs", "telic/frontend/ts/harness.mjs"])
        files += ["telic/frontend/ts/package.json", "telic/frontend/ts/package-lock.json"]
    if native:
        files += ["core/**/*"]
    if lean:
        files += ["telic/lean/**/*.lean", "telic/lean/lean-toolchain", "telic/**/*.proof.lean"]
    return sorted(set(files + patterns + ["telic/lean/lean-toolchain"]))


def _executable_identity(command: str, args: tuple[str, ...] = ("--version",), selected: str | None = None) -> list[str]:
    found = selected if selected and Path(selected).is_file() else shutil.which(command)
    if found is None:
        return [command, "unavailable"]
    path = Path(found).resolve()
    try:
        version = subprocess.run([str(path), *args], capture_output=True, text=True, timeout=10)
        label = (version.stdout or version.stderr).strip()
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
    except (OSError, subprocess.TimeoutExpired) as exc:
        return [command, str(path), f"unavailable:{type(exc).__name__}"]
    return [command, str(path), label, digest]


def runtime_identity(name: str, group: dict) -> dict:
    py = Path(sys.executable).resolve()
    identity = {
        "ci": os.environ.get("TELIC_CI_ID", ""),
        "python": [sys.implementation.name, platform.python_version(), platform.python_build(), str(py), hashlib.sha256(py.read_bytes()).hexdigest()],
    }
    tools = list(group.get("tools", []))
    if group.get("native"):
        tools.extend(["native-z3", "core"])
    if group.get("lean") or name == "proof" and proof_sidecars():
        tools.append("lean")
    for tool in sorted(set(tools)):
        if tool == "native-z3" and "z3-package-sha256=" in identity["ci"]:
            # CI binds the selected executable to the SHA256 in the signed apt
            # package index; apt installs that exact package after planning.
            identity[tool] = [tool, identity["ci"].split("z3-package-sha256=", 1)[1].split()[0]]
        elif tool == "core":
            override = os.environ.get("TELIC_CORE")
            binary = Path(override) if override and Path(override).is_file() else ROOT / "core" / "telic-core"
            identity[tool] = _executable_identity("telic-core", ("--source-hash",), str(binary) if binary.is_file() else None)
        elif tool == "lean":
            from telic.lean import find_lean

            identity[tool] = _executable_identity("lean", ("--version",), find_lean())
        elif tool == "native-z3":
            identity[tool] = _executable_identity("z3", ("--version",), os.environ.get("TELIC_Z3"))
        else:
            identity[tool] = _executable_identity(tool)
    # Python Z3 is installed only after the plan. Its exact package version is
    # constrained in .github/constraints.txt; the solver receipt hashes the
    # loaded shared library once the gate runs.
    identity["python-z3-package"] = "constraints:.github/constraints.txt"
    return identity


_SOUNDNESS = [f"tests/cases/soundness/**/*.{ext}" for ext in ("py", "ts", "tsx", "rs", "swift")]
_ENGINE_CASES = ["tests/cases/corpus.*", "tests/cases/objects/*.py", "tests/cases/objects/*.ts", *_SOUNDNESS,
                 "tests/cases/unmodelled.py"]
_RUST_CASES = ["tests/cases/corpus.rs", "tests/cases/rust_crate/**/*"]
_PROOF_INPUTS = telic_python_sources() + proof_sidecars() + ["core/**/*", "telic.ledger.json"]

_CORPUS_TESTS = {
    "corpus-python": ("tests/test_corpus.py", ["tests/cases/corpus.py"], {"python"}, True),
    "corpus-typescript": ("tests/test_corpus.py", ["tests/cases/corpus.ts"], {"python", "typescript"}, True),
    "corpus-rust": ("tests/test_rust.py", _RUST_CASES, {"python", "rust"}, True),
    "corpus-swift": ("tests/test_swift.py", ["tests/cases/corpus.swift"], {"python", "swift"}, True),
}


def _corpus_group(name: str, tests: list[str]) -> dict:
    test_file, fixtures, languages, replay = _CORPUS_TESTS[name]
    patterns = [test_file, *fixtures]
    tools = [{"typescript": "node", "rust": "rustc", "swift": "swiftc"}[lang] for lang in languages if lang != "python"]
    return {"inputs": test_inputs(patterns, languages=languages, replay=replay) + TEST_SETUP, "tests": tests, "tools": tools}


GROUPS = {
    "proof": {"inputs": _PROOF_INPUTS + PROOF_SETUP, "native": True},
    "corpus-python": _corpus_group("corpus-python", ["tests/test_corpus.py::test_python_corpus", "tests/test_corpus.py::test_python_refutations_are_confirmed_by_execution"]),
    "corpus-typescript": _corpus_group("corpus-typescript", ["tests/test_corpus.py::test_typescript_corpus"]),
    "corpus-rust": _corpus_group("corpus-rust", [f"tests/test_rust.py::{name}" for name in ("test_rust_corpus", "test_rust_refutations_are_real_panics", "test_crate_across_files", "test_crate_file_alone_uses_its_crate", "test_crate_is_valid_rust_and_refutations_replay")]),
    "corpus-swift": _corpus_group("corpus-swift", ["tests/test_swift.py::test_swift_corpus", "tests/test_swift.py::test_swift_refutations_are_real_failures"]),
    "soundness": {"inputs": test_inputs(["tests/test_soundness.py", *_SOUNDNESS], languages={"python", "typescript", "rust", "swift"}, replay=True) + TEST_SETUP, "tests": ["tests/test_soundness.py"], "tools": ["node", "rustc", "swiftc"]},
    "semantics": {"inputs": test_inputs(["tests/test_semantics.py", "tests/test_swift.py", "tests/test_rust.py", "tests/cases/corpus.rs"], languages={"python", "typescript", "rust", "swift"}, replay=True) + TEST_SETUP, "tests": ["tests/test_semantics.py", "tests/test_swift.py::test_swift_integer_semantics_match_swiftc", "tests/test_rust.py::test_proved_functions_hold_when_run"], "tools": ["node", "rustc", "swiftc"]},
    "engine": {"inputs": test_inputs(["tests/test_engine.py", "tests/test_soundness.py", *_ENGINE_CASES], languages={"python", "typescript", "rust", "swift"}, replay=True, native=True) + TEST_SETUP, "tests": [f"tests/test_engine.py::{name}" for name in ("test_engine_agrees_with_python_core", "test_engine_proves_no_exploit", "test_a_field_telic_cannot_model_fails_only_what_touches_it")], "native": True, "tools": ["node", "rustc", "swiftc"]},
    "lean": {"inputs": test_inputs(["tests/test_lean.py"], languages={"python"}, replay=False, lean=True, prover=True) + TEST_SETUP, "tests": ["tests/test_lean.py"], "lean": True, "tools": ["lean"]},
    "cache": {"inputs": test_inputs(["tests/test_cache.py", "tests/test_engine.py", "tests/cases/corpus.*", "tests/cases/objects/*.py", "tests/cases/objects/*.ts"], languages={"python", "typescript", "rust", "swift"}, replay=True, native=True) + TEST_SETUP, "tests": ["tests/test_cache.py", "tests/test_engine.py::test_engine_agrees_with_python_core", "tests/test_engine.py::test_native_query_receipt_ignores_unrelated_term_id_shifts"], "native": True, "tools": ["node"]},
}

def inputs(patterns: list[str]) -> set[str]:
    tracked = set(subprocess.check_output(["git", "ls-files", "--cached", "--others", "--exclude-standard"], cwd=ROOT, text=True).splitlines())
    found: set[str] = set()
    for pattern in patterns:
        if not glob.has_magic(pattern) and not (ROOT / pattern).is_file():
            raise RuntimeError(f"missing required CI evidence input: {pattern}")
        found.update(str(p.relative_to(ROOT)) for p in ROOT.glob(pattern) if p.is_file() and str(p.relative_to(ROOT)) in tracked)
    return found


def baseline(since: str | None) -> dict | None:
    if since:
        tree = subprocess.check_output(["git", "ls-tree", "--name-only", since, "--", "telic.ledger.json"], cwd=ROOT, text=True)
        if tree.strip():
            return json.loads(subprocess.check_output(["git", "show", f"{since}:telic.ledger.json"], cwd=ROOT, text=True))
    path = ROOT / "telic.ledger.json"
    return json.loads(path.read_text()) if path.exists() else None


def key(name: str, since: str | None) -> str:
    setup = PROOF_SETUP if name == "proof" else TEST_SETUP
    paths = inputs(setup + GROUPS[name]["inputs"])
    identity = runtime_identity(name, GROUPS[name])
    h = hashlib.sha256(json.dumps([name, GROUPS[name], identity], sort_keys=True).encode())
    if name == "proof":
        h.update(json.dumps(baseline(since), sort_keys=True).encode())
    for path in sorted(paths):
        h.update(path.encode() + b"\0" + hashlib.sha256((ROOT / path).read_bytes()).digest())
    return h.hexdigest()


def proof(since: str | None, record: bool) -> bool:
    from telic.checker import CheckOptions, check
    from telic.ledger import LEDGER, acceptances, affected_files, changed_files, compare, read_ledger, snapshot, write_ledger

    paths = sorted(str(p.relative_to(ROOT)) for p in (ROOT / "telic").rglob("*.py") if "demo" not in p.relative_to(ROOT).parts)
    old = baseline(since)
    accepted = acceptances(str(ROOT), since)
    if not record:
        committed = read_ledger(str(ROOT / LEDGER))
        if old is None or committed is None:
            raise RuntimeError("no telic.ledger.json: establish the proof baseline with scripts/ci.py --record")
        for c in compare(old, committed, None):
            if c.kind == "regression" and c.id not in accepted:
                print(f"{c.file or LEDGER}: {c.what}", flush=True)
                return False
    scope = None
    if since and not record:
        changed = changed_files(str(ROOT), since)
        compiler = set(_PROOF_INPUTS + PROOF_SETUP)
        if not any(path in compiler or fnmatch.fnmatch(path, "core/**/*") for path in changed):
            scope = affected_files(str(ROOT), changed, old) & set(paths)
            scope |= {k.split("::")[0] for k in (old or {}).get("functions", {}) if not (ROOT / k.split("::")[0]).exists()}
            paths = sorted(p for p in scope if (ROOT / p).exists())
    if not paths and not scope:
        print("proof: no affected implementation files", flush=True)
        return True
    progress = (lambda name: print(name, flush=True)) if os.environ.get("TELIC_CI_DEBUG") else None
    rep = check(paths, CheckOptions(claims_only=True, engine="ox", replay=False, lean_auto=False, infer_auto=False, ui=False, progress=progress, cache_path=str(ROOT / ".telic" / "cache.json")), root=str(ROOT))
    if record:
        for module in rep.modules:
            for message, loc in module.problems:
                print(f"{module.path}:{loc.line}: {message}", flush=True)
    if any(f.timed_out for f in rep.functions):
        print("proof: unfinished obligations cannot establish a CI receipt", flush=True)
        return False
    new = snapshot(rep)
    for f in rep.functions:
        if f.status == "proved" and any((old or {}).get("functions", {}).get(dep, {}).get("status") not in ("proved", "trusted") for dep in f.context_deps):
            new["functions"][f.ref.key]["status"] = "open"
    counts = {status: sum(f["status"] == status for f in new["functions"].values()) for status in sorted({f["status"] for f in new["functions"].values()})}
    print(f"proof: {counts}; {rep.cache_hits} obligations reused, {rep.solved} solved", flush=True)
    if record:
        write_ledger(str(ROOT / LEDGER), new)
        return True
    failures = [c for c in compare(old, new, scope) if c.kind == "regression" and c.id not in accepted]
    for c in failures:
        print(f"{c.file or LEDGER}: {c.what}", flush=True)
    return not failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--plan", action="store_true")
    ap.add_argument("--record", action="store_true")
    ap.add_argument("--since", default=os.environ.get("BASE"))
    ap.add_argument("--group", action="append", choices=GROUPS)
    args = ap.parse_args()
    os.chdir(ROOT)
    if args.record and not args.plan:
        return 0 if proof(None, True) else 1
    receipts = json.loads(RECEIPTS.read_text()) if RECEIPTS.exists() else {}
    keys = {name: key(name, args.since) for name in args.group or (["proof"] if args.record else GROUPS)}
    pending = [name for name, digest in keys.items() if args.record or receipts.get(name) != digest]
    if args.plan:
        sidecars = any("demo" not in p.relative_to(ROOT).parts for p in (ROOT / "telic").rglob("*.proof.lean"))
        outputs = {"needed": bool(pending), "native": any(GROUPS[n].get("native") for n in pending), "lean": any(GROUPS[n].get("lean") for n in pending) or "proof" in pending and sidecars}
        if os.environ.get("GITHUB_OUTPUT"):
            with open(os.environ["GITHUB_OUTPUT"], "a") as out:
                for name, value in outputs.items():
                    out.write(f"{name}={str(value).lower()}\n")
        print(json.dumps({"run": pending, "reused": [name for name in keys if name not in pending]}))
        return 0
    RECEIPTS.parent.mkdir(exist_ok=True)
    for name in keys:
        if name not in pending:
            print(f"{name}: reused verdict on identical inputs", flush=True)
            continue
        print(f"{name}: checking changed inputs", flush=True)
        if name == "proof":
            passed = proof(args.since, False)
        else:
            junit = RECEIPTS.parent / f"ci-{name}.xml"
            result = subprocess.run([sys.executable, "-m", "pytest", "-q", "-rs", f"--junitxml={junit}", *GROUPS[name]["tests"]], cwd=ROOT)
            passed = result.returncode == 0 and not list(ET.parse(junit).iter("skipped"))
        if not passed:
            return 1
        receipts[name] = keys[name]
        RECEIPTS.write_text(json.dumps(receipts, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
