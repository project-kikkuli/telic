"""Measure what telic costs in CI, on a synthetic repository.

Builds N Python + M TypeScript modules from real telic examples, commits them,
and times the situations CI actually sees:

  cold      full check, empty cache (first run, or a toolchain upgrade)
  warm      full check, cache restored (a push to main after a merge)
  pr-none   PR that touches no checkable file
  pr-body   PR that edits one function body
  pr-spec   PR that changes one contract
  pr-many   PR that touches 6 files (the 85th-percentile diff in assay's data)

Usage: python scripts/bench_ci.py [--py 40] [--ts 20] [--out docs/ci-bench.json]
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PY = (ROOT / "examples" / "inventory.py").read_text()
TS = """export function clamp(x: number, lo: number, hi: number): number {
  //@ requires lo <= hi
  //@ ensures lo <= result && result <= hi
  return Math.max(lo, Math.min(x, hi));
}

export function sumList(xs: number[]): number {
  //@ ensures result === sum(xs)
  let total = 0;
  for (const x of xs) {
    total += x;
  }
  return total;
}

export function bsearch(xs: number[], target: number): number {
  //@ requires range(0, xs.length - 1).every(i => xs[i] <= xs[i + 1])
  //@ ensures -1 <= result && result < xs.length
  //@ ensures implies(result >= 0, xs[result] === target)
  let lo = 0;
  let hi = xs.length - 1;
  while (lo <= hi) {
    const mid = Math.floor((lo + hi) / 2);
    if (xs[mid] === target) return mid;
    if (xs[mid] < target) lo = mid + 1;
    else hi = mid - 1;
  }
  return -1;
}

export function discounted(subtotal: number, percent: number): number {
  //@ requires Number.isInteger(subtotal) && Number.isInteger(percent)
  //@ requires subtotal >= 0 && 0 <= percent && percent <= 100
  //@ ensures 0 <= result && result <= subtotal
  return subtotal - Math.floor((subtotal * percent + 50) / 100);
}
"""


def sh(cwd, *cmd, env=None):
    return subprocess.run(list(cmd), cwd=cwd, capture_output=True, text=True, env=env)


def timed(cwd, *args):
    t0 = time.perf_counter()
    out = sh(cwd, sys.executable, "-m", "telic", *args, "--color", "never")
    return round(time.perf_counter() - t0, 2), out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--py", type=int, default=40)
    ap.add_argument("--ts", type=int, default=20)
    ap.add_argument("--out", default=str(ROOT / "docs" / "ci-bench.json"))
    a = ap.parse_args()
    d = Path(tempfile.mkdtemp(prefix="telic-bench-"))
    try:
        (d / "svc").mkdir()
        (d / "web").mkdir()
        for i in range(a.py):
            # make each module textually distinct, so no two share receipts
            (d / "svc" / f"inv{i}.py").write_text(PY.replace("reorder_point", f"reorder_point_{i}"))
        for i in range(a.ts):
            (d / "web" / f"price{i}.ts").write_text(TS.replace("percent", f"pct{i}"))
        for cmd in (["git", "init", "-q", "-b", "main"], ["git", "config", "user.email", "b@x"], ["git", "config", "user.name", "b"]):
            sh(d, *cmd)
        sh(d, sys.executable, "-m", "telic", "init", "--no-hook")
        sh(d, "git", "add", "-A")
        sh(d, "git", "commit", "-qm", "init")
        res: dict[str, float] = {}
        shutil.rmtree(d / ".telic", ignore_errors=True)
        res["cold"], out = timed(d, "check", ".")
        funcs = out.stdout.split("functions ─")[0].count("\n")  # placeholder, replaced below
        res["warm"], out = timed(d, "check", ".")
        head = out.stdout.splitlines()[0] if out.stdout else ""
        sh(d, "git", "checkout", "-qb", "pr")
        (d / "README.md").write_text("docs only\n")
        sh(d, "git", "add", "-A")
        sh(d, "git", "commit", "-qm", "docs")
        res["pr-none"], _ = timed(d, "ci", "--since", "main")
        p = d / "svc" / "inv3.py"
        p.write_text(p.read_text().replace("return sum(levels)", "return sum(levels)  # tidy"))
        p.write_text(p.read_text().replace("    take = min(qty, available(s))", "    take = min(available(s), qty)"))
        sh(d, "git", "commit", "-qam", "body")
        res["pr-body"], out_body = timed(d, "ci", "--since", "main")
        p = d / "svc" / "inv5.py"
        p.write_text(p.read_text().replace("    #@ ensures result >= 0\n    #@ ensures result == sum(levels)", "    #@ ensures result == sum(levels)"))
        sh(d, "git", "commit", "-qam", "spec")
        res["pr-spec"], _ = timed(d, "ci", "--since", "main")
        for i in range(10, 16):
            q = d / "svc" / f"inv{i}.py"
            q.write_text(q.read_text().replace("return s.on_hand - s.reserved", "return s.on_hand - s.reserved + 0"))
        sh(d, "git", "commit", "-qam", "many")
        res["pr-many"], _ = timed(d, "ci", "--since", "main")
        ledger = json.loads((d / "telic.ledger.json").read_text())
        report = {
            "repository": {"python_modules": a.py, "typescript_modules": a.ts, "functions": len(ledger["functions"]), "aims": len(ledger["aims"])},
            "seconds": res,
            "machine": {"python": platform.python_version(), "cpus": os.cpu_count(), "platform": platform.platform()},
            "warm_header": head,
        }
        Path(a.out).write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        del funcs, out_body
    finally:
        shutil.rmtree(d, ignore_errors=True)


if __name__ == "__main__":
    main()
