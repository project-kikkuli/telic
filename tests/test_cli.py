import json
import subprocess
import sys

from conftest import HAS_LEAN, HAS_NODE

import pytest


def telic(*args, cwd):
    return subprocess.run([sys.executable, "-m", "telic", *args], capture_output=True, text=True, cwd=cwd)


def test_json_output_is_actionable(tmp_path):
    (tmp_path / "m.py").write_text("def avg(xs: list[int]) -> float:\n    return sum(xs) / len(xs)\n")
    out = telic("check", "m.py", "--json", "--no-cache", cwd=tmp_path)
    assert out.returncode == 1
    data = json.loads(out.stdout)
    assert data["ok"] is False
    (fn,) = data["functions"]
    (ob,) = [o for o in fn["obligations"] if o["status"] != "proved"]
    assert ob["kind"] == "div" and ob["line"] == 2
    assert ob["counterexample"] == "avg([])"
    assert ob["replay"]["confirmed"] is True


def test_exit_codes(tmp_path):
    (tmp_path / "ok.py").write_text("def f(x: int) -> int:\n    #@ ensures result == x\n    return x\n")
    assert telic("check", "ok.py", "--no-cache", cwd=tmp_path).returncode == 0
    (tmp_path / "open.py").write_text("def g(n: int) -> int:\n    #@ ensures result == 1\n    while n != 1:\n        n = n // 2 if n % 2 == 0 else 3 * n + 1\n    return n\n")
    assert telic("check", "open.py", "--no-cache", cwd=tmp_path).returncode == 0
    assert telic("check", "open.py", "--no-cache", "--strict", cwd=tmp_path).returncode == 1


JSON_TREE = """from typing import Any


#@ trusted
#@ ensures result >= 0
def depth(v: Any) -> int: ...


#@ trusted
#@ ensures result == (isinstance(t, dict) and "kind" in t and (t["kind"] == "leaf" or t["kind"] == "node" and "left" in t and wf_tree(t["left"]) and depth(t["left"]) < depth(t)))
def wf_tree(t: Any) -> bool: ..."""

INFERRED = [
    ("def f(n: int) -> int:\n    if n <= 0:\n        return 0\n    return f(n - 1)\n", {"f": "n"}),
    ("def a(m: int, n: int) -> int:\n    #@ requires m >= 0 and n >= 0\n    if m == 0 or n == 0:\n        return 0\n    if n > 1:\n        return a(m, n - 1)\n    return a(m - 1, 5)\n", {"a": "[m, n]"}),
    (JSON_TREE + "\n\ndef leaves(t: dict[str, Any]) -> int:\n    #@ requires wf_tree(t)\n    if t['kind'] == 'leaf':\n        return 1\n    return leaves(t['left'])\n", {"leaves": "depth(t)"}),
    ("def e(n: int) -> bool:\n    #@ requires n >= 0\n    if n == 0:\n        return True\n    return o(n - 1)\n\n\ndef o(n: int) -> bool:\n    #@ requires n >= 0\n    if n == 0:\n        return False\n    return e(n - 1)\n", {"e": "n", "o": "n"}),
]


@pytest.mark.parametrize("src,want", INFERRED)
def test_inferred_measures_are_reported_and_cached(tmp_path, src, want):
    (tmp_path / "m.py").write_text(src)
    for _ in range(2):  # the second run rebuilds them from the cache
        data = json.loads(telic("check", "m.py", "--json", cwd=tmp_path).stdout)
        checked = [f for f in data["functions"] if f["status"] != "trusted"]
        assert {f["function"]: f["inferred"]["measure"] for f in checked} == want
        assert all(f["status"] == "proved" for f in checked)
    out = telic("check", "m.py", "-v", "--color", "never", cwd=tmp_path).stdout
    for m in want.values():
        assert f"inferred @decreases {m}" in out


def test_explain_shows_formula(tmp_path):
    (tmp_path / "m.py").write_text("def f(x: int) -> int:\n    #@ requires x > 0\n    #@ ensures result > 1\n    return x + 1\n")
    out = telic("explain", "f", "m.py", "--no-cache", cwd=tmp_path)
    assert "⊢" in out.stdout and "f/ensures@3>4" in out.stdout


@pytest.mark.skipif(not (HAS_NODE and HAS_LEAN), reason="the full demo needs Node and Lean")
def test_demo_runs_green():
    out = subprocess.run([sys.executable, "-m", "telic", "demo", "--no-pause", "--color", "never"], capture_output=True, text=True, timeout=600)
    assert out.returncode == 0, out.stderr
    text = out.stdout
    assert "✗ REFUTED refund_amount" in text
    assert "✗ DIVERGES discounted_total ≡ displayTotal" in text
    assert "is stale" in text
    tail = text.rsplit("the whole shop", 1)[1]
    assert "6 proved" in tail and "refuted" not in tail.split("aims", 1)[1]


def test_html_report(tmp_path):
    (tmp_path / "m.py").write_text("#@ aim POS: Results are positive.\n\ndef f(x: int) -> int:\n    #@ requires x > 0\n    #@ aim POS\n    #@ ensures result > 0\n    return x\n")
    out = telic("report", "m.py", "--no-cache", "-o", "r.html", cwd=tmp_path)
    assert out.returncode == 0, out.stderr
    page = (tmp_path / "r.html").read_text()
    assert page.startswith("<!doctype html>") and "POS" in page and "✓ proved" in page
