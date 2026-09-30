"""Apply each seeded regression to a copy of an example app, one telic check at a time, and report which are caught.

    uv run --extra ui python examples/ui/run_seeded.py [notes-react tasks-svelte] [--work DIR] [--patch NAME]

The app is copied to DIR/<app> (default: a new temp dir) and `npm ci` runs there
once; each patch is applied, checked and reverted in that copy, never in the repo.
Runs are strictly sequential: one `telic check` process at a time.

A bug is caught when a lemma the unpatched app does not refute comes out refuted
or vacuous; a lemma that only goes open is not a catch. The
outcome of each patch is compared with seeded/expected.json; a difference exits 1.
Each full report is kept in DIR/<app>/.telic/seeded/<patch>.json.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def lemmas(app: Path, save: str) -> dict[str, dict]:
    out = subprocess.run(
        [sys.executable, "-m", "telic", "check", str(app), "--json", "--root", str(app)],
        capture_output=True,
        text=True,
    )
    if not out.stdout.strip():
        sys.exit(f"{app.name}/{save}: telic check printed no report\n{out.stderr[-2000:]}")
    report = json.loads(out.stdout)
    dump = app / ".telic" / "seeded" / f"{save}.json"
    dump.parent.mkdir(parents=True, exist_ok=True)
    dump.write_text(json.dumps(report, indent=2))
    ui = report.get("ui") or {}
    return {lem["name"]: lem for lem in ui.get("lemmas", [])}


def patch(app: Path, diff: Path, reverse: bool = False) -> None:
    subprocess.run(["patch", "-s", "-p1", "-d", str(app), "-i", str(diff)] + (["-R"] if reverse else []), check=True)


def copy(src: Path, work: Path) -> Path:
    dst = work / src.name
    if not dst.exists():
        shutil.copytree(src, dst, ignore=shutil.ignore_patterns("node_modules", ".telic"))
        subprocess.run(["npm", "ci", "--no-audit", "--no-fund", "--silent"], cwd=dst, check=True)
    return dst


BAD = {"refuted", "vacuous"}


def run(src: Path, work: Path, only: str | None) -> bool:
    app = copy(src, work)
    base = lemmas(app, "base")
    pinned = src / "seeded" / "expected.json"
    expected = json.loads(pinned.read_text()) if pinned.exists() else {}
    ok = True
    for diff in sorted((src / "seeded").glob(f"{only or '*'}.patch")):
        patch(app, diff)
        try:
            now = lemmas(app, diff.stem)
        finally:
            patch(app, diff, reverse=True)
        changed = {n: now[n] for n in now if now[n]["status"] in BAD and base.get(n, {}).get("status") != now[n]["status"]}
        failed = next((lem["detail"] for lem in now.values() if lem["status"] == "error"), None)
        if failed:
            ok = False
            print(f"{src.name}/{diff.stem}: no verdict: {failed}", flush=True)
            continue
        caught = bool(changed)
        want = expected.get(diff.stem)
        mark = "" if want is None or want == caught else "  (expected " + ("caught" if want else "missed") + ")"
        ok &= mark == ""
        print(f"{src.name}/{diff.stem}: {'caught' if caught else 'missed'}{mark}", flush=True)
        for n, lem in changed.items():
            print(f"    {n}: {base.get(n, {}).get('status')} -> {lem['status']}: {lem.get('detail')}")
            for i, step in enumerate(lem.get("trace") or [], 1):
                print(f"      {i}. {step}")
    return ok


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("apps", nargs="*")
    ap.add_argument("--work", type=Path)
    ap.add_argument("--patch", help="run only the patch with this name, e.g. 03-confirm-trap")
    args = ap.parse_args()
    work = (args.work or Path(tempfile.mkdtemp(prefix="telic-seeded-"))).resolve()
    names = args.apps or sorted(p.parent.parent.name for p in HERE.glob("*/seeded/*.patch"))
    names = list(dict.fromkeys(names))
    sys.exit(0 if all([run(HERE / n if "/" not in n else Path(n).resolve(), work, args.patch) for n in names]) else 1)
