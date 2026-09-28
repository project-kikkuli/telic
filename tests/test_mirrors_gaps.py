from telic.checker import CheckOptions
from telic.gaps import find_gaps

from conftest import needs_node, run_check

SERVER = """
def discounted(subtotal: int, percent: int) -> int:
    #@ requires subtotal >= 0 and 0 <= percent <= 100
    #@ ensures 0 <= result <= subtotal
    return subtotal - round(subtotal * percent / 100)
"""

WEB = """export function discounted(subtotal: number, percent: number): number {
  //@ requires Number.isInteger(subtotal) && Number.isInteger(percent)
  //@ requires subtotal >= 0 && 0 <= percent && percent <= 100
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
