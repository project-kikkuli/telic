"""A replay that only fails by reading a stand-in for a value of a type telic
does not model (made up, not a value of that type) confirms nothing. A
stand-in for an unknown/any input is a real value of that type, and a run
on real values still confirms."""

import pytest

from telic.checker import CheckOptions, check

from conftest import HAS_NODE

TS_REC = "type Rec = { n: number; f: () => void };\n"
CASES = [
    ("u.ts", TS_REC + "export function attr(r: Rec): number {\n  //@ ensures result === r.n\n  return r.n;\n}\n", "attr", "open"),
    ("u.ts", TS_REC + "export function deep(r: Rec): number {\n  //@ ensures result === r.n + 1\n  return r.n + 1;\n}\n", "deep", "open"),
    ("u.ts", "export function anyAttr(r: any): number {\n  //@ ensures result === r.n\n  return r.n;\n}\n", "anyAttr", "refuted"),
    ("u.ts", "export function bug(r: Map<string, number>, k: number): number {\n  //@ ensures result === k\n  return k + 1;\n}\n", "bug", "refuted"),
    ("u.py", "def attr(r: 'Widget') -> int:\n    #@ ensures result == r.n\n    return r.n\n", "attr", "open"),
    ("u.py", "def bug(r: 'Widget', k: int) -> int:\n    #@ ensures result == k\n    return k + 1\n", "bug", "refuted"),
]


@pytest.mark.parametrize("name,src,fn,status", CASES)
def test_stand_ins_confirm_nothing(tmp_path, name, src, fn, status):
    if name.endswith(".ts") and not HAS_NODE:
        pytest.skip("Node.js not available")
    f = tmp_path / name
    f.write_text(src)
    rep = check([str(f)], CheckOptions(cache_path=None, lean=False), root=str(tmp_path))
    r = next(r for r in rep.functions if r.fn.name == fn)
    assert r.status == status
    replays = [v.replay for v in r.verdicts if v.replay is not None]
    assert replays and all(x.confirmed == (status == "refuted") for x in replays)


def test_a_failing_input_is_shrunk_to_one_that_fails_the_same_way():
    import types

    from telic.replay_harness import shrink
    from telic.runtime import ContractViolation

    def f(xs, n):
        if any(x > 1000 for x in xs) and n > 50:
            raise IndexError("boom")
        return 0

    args, out = shrink(f, [[5, 2000, 7, 3000] * 60, 9000], {"crash": "IndexError"}, types.SimpleNamespace(__file__="none"), ContractViolation, "f")
    assert args == [[1001], 51] and out["crash"] == "IndexError"
