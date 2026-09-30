import pytest

from telic.checker import CheckOptions
from telic.gaps import find_gaps

from conftest import needs_node, run_check

SERVER = """
def discounted(subtotal: int, percent: int) -> int:
    #@ requires 0 <= subtotal <= 1000000 and 0 <= percent <= 100
    #@ ensures 0 <= result <= subtotal
    return subtotal - round(subtotal * percent / 100)
"""

WEB = """export function discounted(subtotal: number, percent: number): number {
  //@ requires Number.isInteger(subtotal) && Number.isInteger(percent)
  //@ requires subtotal >= 0 && subtotal <= 1000000 && 0 <= percent && percent <= 100
  //@ mirrors ../server/pricing.py::discounted
  //@ ensures 0 <= result && result <= subtotal
  return subtotal - Math.round((subtotal * percent) / 100);
}
"""


@needs_node
def test_mirror_divergence_is_found_and_confirmed(tmp_path):
    rep = run_check(tmp_path, {"server/pricing.py": SERVER, "web/pricing.ts": WEB})
    assert all(f.status == "proved" for f in rep.functions)
    (m,) = rep.mirrors
    assert m.status == "refuted"
    assert m.witness["replay"]["confirmed"]
    assert "banker" in m.explanation
    assert not rep.ok


@needs_node
def test_mirror_file_is_loaded_automatically(tmp_path):
    (tmp_path / "server").mkdir()
    (tmp_path / "server/pricing.py").write_text(SERVER)
    rep = run_check(tmp_path, {"web/pricing.ts": WEB})
    assert {m.path for m in rep.modules} == {"web/pricing.ts", "server/pricing.py"}


@needs_node
def test_mirror_equivalence_is_proved(tmp_path):
    server = SERVER.replace("round(subtotal * percent / 100)", "(subtotal * percent + 50) // 100")
    web = WEB.replace("Math.round((subtotal * percent) / 100)", "Math.floor((subtotal * percent + 50) / 100)")
    rep = run_check(tmp_path, {"server/pricing.py": server, "web/pricing.ts": web})
    (m,) = rep.mirrors
    assert m.status == "proved" and m.method == "smt"
    assert rep.ok


def test_mirror_between_python_loops_uses_testing(tmp_path):
    a = """
def total(xs: list[int]) -> int:
    t = 0
    for x in xs:
        t += x
    return t


def total2(xs: list[int]) -> int:
    #@ mirrors a.py::total
    t = 0
    for x in xs:
        if x > 0:
            t += x
    return t
"""
    rep = run_check(tmp_path, {"a.py": a})
    (m,) = rep.mirrors
    assert m.status == "refuted" and m.method == "testing"


SPLIT_PY = """
def share(amount: int, parts: int, i: int) -> int:
    #@ requires amount >= 0 and parts >= 1 and 0 <= i < parts
    #@ ensures result >= 0
    if i < amount % parts:
        return amount // parts + 1
    return amount // parts


def split(amount: int, parts: int) -> list[int]:
    #@ requires amount >= 0 and parts >= 1
    #@ ensures len(result) == parts
    #@ ensures all(result[i] == share(amount, parts, i) for i in range(parts))
    out: list[int] = []
    for i in range(parts):
        #@ invariant len(out) == i
        #@ invariant all(out[k] == share(amount, parts, k) for k in range(i))
        out.append(share(amount, parts, i))
    return out
"""

SPLIT_TS = """type int = number;
function shareOf(amount: int, parts: int, i: int): int {
  //@ requires Number.isSafeInteger(amount) && amount >= 0 && parts >= 1 && 0 <= i && i < parts
  const base = Math.floor(amount / parts);
  return i < amount % parts ? base + 1 : base;
}

export function splitAll(amount: int, parts: int): int[] {
  //@ mirrors ../server/split.py::split
  //@ requires Number.isSafeInteger(amount) && amount >= 0 && parts >= 1
  //@ ensures result.length === parts
  //@ ensures range(0, parts).every(i => result[i] === shareOf(amount, parts, i))
  const out: int[] = [];
  for (let i = 0; i < parts; i++) {
    //@ invariant out.length === i
    //@ invariant range(0, i).every(k => out[k] === shareOf(amount, parts, k))
    out.push(shareOf(amount, parts, i));
  }
  return out;
}
"""


@needs_node
@pytest.mark.parametrize("web,status,method", [(SPLIT_TS, "proved", "contracts"), (SPLIT_TS.replace("base + 1 : base", "base : base + 1"), "refuted", "testing")])
def test_mirror_of_loops_is_proved_from_their_contracts(tmp_path, web, status, method):
    rep = run_check(tmp_path, {"server/split.py": SPLIT_PY, "web/split.ts": web})
    (m,) = rep.mirrors
    assert (m.status, m.method) == (status, method), m.reason


@needs_node
def test_a_proved_helper_mirror_is_a_lemma_for_the_loops_using_it(tmp_path):
    py = SPLIT_PY.replace("if i < amount % parts:\n        return amount // parts + 1\n    return amount // parts", "base = amount // parts\n    if i < amount % parts:\n        return base + 1\n    return base")
    web = SPLIT_TS.replace("function shareOf(amount: int, parts: int, i: int): int {\n", "export function shareOf(amount: int, parts: int, i: int): int {\n  //@ mirrors ../server/split.py::share\n")
    rep = run_check(tmp_path, {"server/split.py": py, "web/split.ts": web})
    assert sorted((m.a.fn.name, m.status, m.method) for m in rep.mirrors) == [("share", "proved", "smt"), ("split", "proved", "contracts")]


REFUND = """
def refund(paid: int, refunded: int, requested: int) -> int:
    #@ requires 0 <= refunded <= paid and requested >= 0
    #@ ensures 0 <= result <= paid - refunded
    remaining = paid - refunded
    if requested > remaining:
        return remaining
    return requested
"""


def test_gaps_find_accepted_wrong_versions(tmp_path):
    (tmp_path / "r.py").write_text(REFUND)
    res = find_gaps([str(tmp_path / "r.py")], CheckOptions(cache_path=None), str(tmp_path))
    (fg,) = res
    assert fg.gaps, "weak contract should admit mutants"
    assert any("return 0" in g.mutant.after for g in fg.gaps)


def test_gaps_close_when_contract_is_strengthened(tmp_path):
    strong = REFUND.replace("#@ ensures 0 <= result <= paid - refunded", "#@ ensures result == min(requested, paid - refunded)")
    (tmp_path / "r.py").write_text(strong)
    res = find_gaps([str(tmp_path / "r.py")], CheckOptions(cache_path=None), str(tmp_path))
    (fg,) = res
    assert not fg.gaps
    assert fg.killed >= 8


def test_gaps_leave_specification_helpers_to_the_contracts_using_them(tmp_path):
    (tmp_path / "s.py").write_text(SPLIT_PY)
    res = {fg.ref.fn.name: fg for fg in find_gaps([str(tmp_path / "s.py")], CheckOptions(cache_path=None), str(tmp_path))}
    assert res["split"].total and not res["split"].gaps
    assert "specification" in res["share"].skipped
