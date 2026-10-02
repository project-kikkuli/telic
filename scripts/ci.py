"""Reuse proof receipts; audit verifier semantics only when their inputs change."""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import platform
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
RECEIPTS = ROOT / ".telic" / "ci-verdicts.json"
HARNESS = ["scripts/ci.py", ".github/workflows/ci.yml", ".github/constraints.txt", "pyproject.toml", "tests/conftest.py"]
KERNEL = [f"telic/{name}.py" for name in (
    "__init__", "ir", "contracts", "program", "logic", "vcgen", "infer", "smt", "checker",
    "jobs", "slots", "irjson", "engine", "history", "lifecycle", "equiv", "replay", "replay_harness",
    "lean", "prover", "render_expr", "aim", "oracle", "gaps", "propose", "phrase", "ledger",
)] + ["telic/ui/spec.py"]
FRONTENDS = {
    "python": ["telic/frontend/__init__.py", "telic/frontend/python*.py", "telic/frontend/aim_file.py"],
    "typescript": ["telic/frontend/typescript.py", "telic/frontend/ts/*.mjs", "telic/frontend/ts/package*.json"],
    "rust": ["telic/frontend/rust*.py"],
    "swift": ["telic/frontend/swift*.py"],
}
ALL_FRONTENDS = [p for paths in FRONTENDS.values() for p in paths]
GROUPS = {
    "proof": {"inputs": ["telic/**/*.py", "telic/**/*.proof.lean", "telic/frontend/ts/*.mjs", "telic/frontend/ts/package*.json", "core/*.ml", "core/Makefile", "telic/lean/*", "telic.ledger.json"], "native": True},
    "corpus-python": {"inputs": KERNEL + FRONTENDS["python"] + ["tests/test_corpus.py", "tests/cases/corpus.py"], "tests": ["tests/test_corpus.py::test_python_corpus", "tests/test_corpus.py::test_python_refutations_are_confirmed_by_execution"]},
    "corpus-typescript": {"inputs": KERNEL + FRONTENDS["python"] + FRONTENDS["typescript"] + ["tests/test_corpus.py", "tests/cases/corpus.ts"], "tests": ["tests/test_corpus.py::test_typescript_corpus"]},
    "corpus-rust": {"inputs": KERNEL + FRONTENDS["python"] + FRONTENDS["rust"] + ["tests/test_rust.py", "tests/cases/corpus.rs", "tests/cases/rust_crate/**/*"], "tests": [f"tests/test_rust.py::{name}" for name in ("test_rust_corpus", "test_rust_refutations_are_real_panics", "test_crate_across_files", "test_crate_file_alone_uses_its_crate", "test_crate_is_valid_rust_and_refutations_replay")]},
    "corpus-swift": {"inputs": KERNEL + FRONTENDS["python"] + FRONTENDS["swift"] + ["tests/test_swift.py", "tests/cases/corpus.swift"], "tests": ["tests/test_swift.py::test_swift_corpus", "tests/test_swift.py::test_swift_refutations_are_real_failures"]},
    "soundness": {"inputs": KERNEL + ALL_FRONTENDS + ["core/*.ml", "tests/test_soundness.py", "tests/cases/soundness/**/*"], "tests": ["tests/test_soundness.py"], "native": True},
    "semantics": {"inputs": KERNEL + ALL_FRONTENDS + ["tests/test_semantics.py", "tests/test_swift.py", "tests/test_rust.py", "tests/cases/corpus.rs"], "tests": ["tests/test_semantics.py", "tests/test_swift.py::test_swift_integer_semantics_match_swiftc", "tests/test_rust.py::test_proved_functions_hold_when_run"]},
    "engine": {"inputs": KERNEL + ALL_FRONTENDS + ["core/*.ml", "core/Makefile", "tests/test_engine.py", "tests/test_soundness.py", "tests/cases/**/*"], "tests": ["tests/test_engine.py"], "native": True},
    "lean": {"inputs": KERNEL + ALL_FRONTENDS + ["telic/lean/*", "tests/test_lean.py"], "tests": ["tests/test_lean.py"], "lean": True},
}


def inputs(patterns: list[str]) -> set[str]:
    tracked = set(subprocess.check_output(["git", "ls-files", "--cached", "--others", "--exclude-standard"], cwd=ROOT, text=True).splitlines())
    return {str(p.relative_to(ROOT)) for pattern in patterns for p in ROOT.glob(pattern) if p.is_file() and str(p.relative_to(ROOT)) in tracked}


def baseline(since: str | None) -> dict | None:
    if since:
        tree = subprocess.check_output(["git", "ls-tree", "--name-only", since, "--", "telic.ledger.json"], cwd=ROOT, text=True)
        if tree.strip():
            return json.loads(subprocess.check_output(["git", "show", f"{since}:telic.ledger.json"], cwd=ROOT, text=True))
    path = ROOT / "telic.ledger.json"
    return json.loads(path.read_text()) if path.exists() else None


def key(name: str, since: str | None) -> str:
    paths = inputs(HARNESS + GROUPS[name]["inputs"])
    identity = os.environ.get("TELIC_CI_ID", f"{platform.system()} {platform.machine()} {platform.python_version()}")
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
        compiler = KERNEL + ALL_FRONTENDS + HARNESS + ["core/*.ml", "core/Makefile", "telic/lean/*"]
        if not any(fnmatch.fnmatch(path, pattern) for path in changed for pattern in compiler):
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
    if args.record:
        return 0 if proof(None, True) else 1
    receipts = json.loads(RECEIPTS.read_text()) if RECEIPTS.exists() else {}
    keys = {name: key(name, args.since) for name in args.group or GROUPS}
    pending = [name for name, digest in keys.items() if receipts.get(name) != digest]
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
