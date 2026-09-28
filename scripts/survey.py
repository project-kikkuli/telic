"""What does telic fail to model in real code? Lowers every file under the
given directories and tallies checkable vs unsupported functions and the
reasons, so coverage work goes where real code needs it."""

from __future__ import annotations

import ast
import collections
import os
import re
import sys

from telic.checker import language_of, load_modules


def normalize(msg: str) -> str:
    msg = re.sub(r"'[^']*'", "'…'", msg)
    msg = re.sub(r"\d+", "N", msg)
    return msg[:90]


def main(paths: list[str]) -> None:
    root = os.path.commonpath([os.path.abspath(p) for p in paths])
    mods = load_modules(paths, root)
    total = ok = 0
    reasons: collections.Counter = collections.Counter()
    for m in mods:
        for msg, _ in m.problems:
            reasons["[module] " + normalize(msg)] += 1
        if m.language == "python":
            tree = ast.parse(m.source)
            defs = [n for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
            top = set(m.functions)
            for d in defs:
                if d.name not in top or d not in tree.body:
                    total += 1
                    kind = "method" if any(isinstance(p, ast.ClassDef) and d in p.body for p in ast.walk(tree)) else "async" if isinstance(d, ast.AsyncFunctionDef) else "nested"
                    reasons[f"[not a top-level function] {kind}"] += 1
        for f in m.functions.values():
            total += 1
            if f.unsupported:
                reasons[normalize(f.unsupported[0][0])] += 1
            else:
                ok += 1
    print(f"{len(mods)} files, {total} functions, {ok} modelled ({100 * ok / max(total, 1):.0f}%)")
    for r, n in reasons.most_common(30):
        print(f"{n:5d}  {r}")


if __name__ == "__main__":
    main(sys.argv[1:])
