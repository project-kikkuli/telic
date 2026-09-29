"""Intents are requirements above lemmas: EARS shape, two-sided links,
statuses that never say 'proved', reviews and judgments pinned by digest."""

import json
import os
import shutil
import sys
from pathlib import Path

from telic.checker import CheckOptions, check
from telic.intent import accept, ears_problems, judge, split_by

CASES = Path(__file__).parent / "cases" / "intents"


def intents(root: Path):
    rep = check([str(root / "app.py")], CheckOptions(cache_path=None, lean=False, replay=False), root=str(root))
    return rep, {i.id: i for i in rep.intents}


def test_ears_lint():
    assert ears_problems("WHEN a refund is requested, the shop shall refund at most what was paid.") == []
    assert ears_problems("The shop shall log every refund.") == []
    assert ears_problems("IF the card is declined THEN the shop shall keep the order open.") == []
    assert any("THEN" in p for p in ears_problems("IF the card is declined the shop shall wait."))
    assert any("'shall'" in p for p in ears_problems("Refunds are capped."))
    assert any("more than one sentence" in p for p in ears_problems("The shop shall refund. It shall log."))


def test_by_list_parsing():
    assert split_by("The shop shall pay. by: a, b.c, web/x.ts::f") == ("The shop shall pay.", ["a", "b.c", "web/x.ts::f"])
    assert split_by("The shop shall pay.") == ("The shop shall pay.", [])


def test_statuses_and_two_sided_links(tmp_path):
    shutil.copy(CASES / "app.py", tmp_path / "app.py")
    _, got = intents(tmp_path)
    cap = got["CAP"]
    assert cap.status == "backed" and cap.proved == 2  # refund's ensures and stray's tagged clause
    msgs = " | ".join(cap.pointers)
    assert "'audit' is listed in by: but does not cite CAP" in msgs
    assert "stray cites CAP but is not in its by: list" in msgs
    assert got["LOOSE"].ears  # not an EARS sentence
    assert got["LONELY"].status == "unbacked"
    assert got["UNDECLARED-ONE"].status == "undeclared"
    assert all(i.status != "proved" for i in got.values())


def test_review_goes_stale_when_lemmas_change(tmp_path):
    shutil.copy(CASES / "app.py", tmp_path / "app.py")
    _, got = intents(tmp_path)
    accept(str(tmp_path), got["CAP"], "ana")
    _, got = intents(tmp_path)
    assert got["CAP"].coverage == {"kind": "reviewed", "by": "ana", "fresh": True}
    src = (tmp_path / "app.py").read_text().replace("#@ ensures result <= paid", "#@ ensures result <= paid + 1")
    (tmp_path / "app.py").write_text(src)
    _, got = intents(tmp_path)
    assert got["CAP"].coverage["fresh"] is False


def test_judge_is_cached_and_labelled(tmp_path):
    shutil.copy(CASES / "app.py", tmp_path / "app.py")
    counter = tmp_path / "calls"
    # a cmd: oracle reads the typed request on stdin and answers every noul question "no"
    script = tmp_path / "oracle.py"
    script.write_text(
        "import json, sys\n"
        f"open({str(counter)!r}, 'a').write('x')\n"
        "req = json.load(sys.stdin)\n"
        "assert req['task'] == 'coverage' and 'covers' in req['questions']\n"
        "print(json.dumps({'answers': {k: {'noul': 0.1} for k in req['questions']}}))\n"
    )
    spec = f"cmd:{sys.executable} {script}"
    _, got = intents(tmp_path)
    judge(str(tmp_path), [got["CAP"]], oracle=spec)
    cov = got["CAP"].coverage
    assert cov["kind"] == "judged" and cov["verdict"] == "insufficient"
    assert cov["model"].startswith("cmd:") and cov["missing"]  # labelled with the oracle, and says which part is missing
    _, got = intents(tmp_path)  # a fresh run shows the cached judgment
    assert got["CAP"].coverage["kind"] == "judged"
    judge(str(tmp_path), [got["CAP"]], oracle=spec)
    assert counter.read_text() == "x"  # asked once
