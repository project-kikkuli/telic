from telic.frontend.python import lower_python

from conftest import needs_node, run_check


def test_stray_contract_is_a_problem():
    m = lower_python("x.py", "x = 1\n#@ ensures x > 0\n")
    assert any("stray" in msg for msg, _ in m.problems)


def test_unknown_keyword_is_a_problem():
    m = lower_python("x.py", "def f(x: int) -> int:\n    #@ ensure x > 0\n    return x\n")
    assert any("unknown contract keyword" in msg for msg, _ in m.problems)


def test_unsupported_constructs_are_reported_with_lines():
    src = "def f(x: int) -> int:\n    global y\n    return x\n"
    f = lower_python("x.py", src).functions["f"]
    assert f.unsupported and f.unsupported[0][1].line == 2


def test_missing_annotation_is_reported():
    # Unannotated code is gradual: the parameter is opaque, not an error.
    m = lower_python("x.py", "def f(x):\n    return x\n")
    assert not m.problems
    assert str(m.functions["f"].params[0].ty) == "opaque"


def test_list_alias_is_rejected():
    src = "def f(xs: list[int]) -> int:\n    ys = xs\n    ys[0] = 1\n    return 0\n"
    f = lower_python("x.py", src).functions["f"]
    assert any("alias" in msg for msg, _ in f.unsupported)


def test_intents_declared_linked_and_statused(tmp_path):
    src = """
#@ intent CAP: Results never exceed the cap.
#@ intent LATER: Something nobody formalized yet.

def capped(x: int, cap: int) -> int:
    #@ requires cap >= 0
    #@ intent CAP
    #@ ensures result <= cap
    return min(x, cap)


def tagged(x: int) -> int:
    #@ [GHOST] ensures result == x
    return x
"""
    rep = run_check(tmp_path, {"i.py": src})
    st = {i.id: i.status for i in rep.intents}
    assert st == {"CAP": "backed", "LATER": "unbacked", "GHOST": "undeclared"}


def test_function_without_contract_still_gets_safety_checks(tmp_path):
    rep = run_check(tmp_path, {"s.py": "def avg(xs: list[int]) -> float:\n    return sum(xs) / len(xs)\n"})
    (f,) = rep.functions
    assert f.status == "refuted"
    assert f.verdicts[0].replay.confirmed


@needs_node
def test_typescript_integrality_inference(tmp_path):
    src = """export function f(xs: number[]): number {
  let count = 0;
  let total = 0;
  for (const x of xs) {
    count += 1;
    total += x;
  }
  return count;
}
"""
    rep = run_check(tmp_path, {"t.ts": src})
    fn = rep.functions[0].fn
    assert str(fn.locals["count"]) == "int" and str(fn.locals["total"]) == "real"
    assert str(fn.ret) == "int"
