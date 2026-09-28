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
        seen: set[str] = set()
        if m.language == "python":
            tree = ast.parse(m.source)
            owner = {}
            for c in ast.walk(tree):
                if isinstance(c, ast.ClassDef):
                    for d in c.body:
                        if isinstance(d, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            owner[d] = c.name
            for d in ast.walk(tree):
                if not isinstance(d, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                key = f"{owner[d]}.{d.name}" if d in owner else d.name if d in tree.body else None
                if key is not None and key in m.functions:
                    continue
                total += 1
                kind = "async" if isinstance(d, ast.AsyncFunctionDef) else "method of an unmodelled class" if d in owner else "nested function" if key is None else "signature"
                reasons[f"[not lowered] {kind}"] += 1
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
