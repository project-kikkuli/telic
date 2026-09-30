"""Code that once made telic fail with an internal error reaches a verdict,
or an honest 'unsupported' with its reason, on both engines."""

from pathlib import Path

import pytest

from telic import engine
from telic.checker import CheckOptions, check

from conftest import HAS_NODE
from test_corpus import expectations

CASES = Path(__file__).parent / "cases"
ENGINES = ["python"] + (["ox"] if engine.binary() is not None else [])


@pytest.mark.parametrize("eng", ENGINES)
@pytest.mark.parametrize("name", ["errors.py", "errors.ts"])
def test_reaches_a_verdict(name, eng):
    if name.endswith(".ts") and not HAS_NODE:
        pytest.skip("Node.js not available")
    path = CASES / name
    rep = check([str(path)], CheckOptions(cache_path=None, lean=False, replay=False, engine=eng), root=str(path.parent))
    got = {f.fn.name: f for f in rep.functions}
    bad = [f"{n}: expected {want}, got {got[n].status} {got[n].problems}" for n, want in expectations(path).items() if got[n].status != want]
    assert not bad, "\n".join(bad)
    assert all(p for f in rep.functions if f.status == "unsupported" for p, _ in f.problems)
