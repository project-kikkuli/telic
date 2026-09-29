"""intents.md: cross-file intents scoped to a directory, one ID space with
comments, found by `telic intents --for`, and carried into the ledger."""

import json
from pathlib import Path

import pytest

from telic.checker import CheckOptions, check
from telic.cli import main
from telic.frontend.intents_md import lower_intents_md
from telic.intent import intents_for
from telic.ledger import affected_files

SAME = "WHEN a charge is made, the shop shall charge a non-negative amount."


def fn(name: str, iid: str | None) -> str:
    cite = f"    #@ intent {iid}\n" if iid else ""
    return f"def {name}(x: int) -> int:\n    #@ requires x >= 0\n{cite}    #@ ensures result >= 0\n    return x\n\n\n"


def tree(root: Path, files: dict[str, str]) -> Path:
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return root


def md(*intents: tuple[str, str, str]) -> str:
    return "# Intents\n\nFree prose.\n\n" + "".join(f"## {i}\n{s}\n" + (f"by: {b}\n" if b else "") + "\n" for i, s, b in intents)


def report(root: Path, paths=(".",)):
    rep = check([str(root / p) for p in paths], CheckOptions(cache_path=None, lean=False, replay=False), root=str(root))
    return rep, {i.id: i for i in rep.intents}


def run(root: Path, *args: str, capsys=None) -> tuple[int, str]:
    code = main(["intents", *args, "--root", str(root), "--no-cache", "--no-lean", "--no-replay"] + [str(root)] * (not any(a.startswith("--for") for a in args)))
    return code, capsys.readouterr().out if capsys else ""


@pytest.mark.parametrize(
    "source, decls, problems",
    [
        (md(("CAP", SAME, "a, b.c")), [("CAP", f"{SAME} by: a, b.c", 5)], []),
        ("## CAP\nWHEN a charge is made,\nthe shop shall charge.\n", [("CAP", "WHEN a charge is made, the shop shall charge.", 1)], []),
        ("## CAP\n\n## NEXT\nThe shop shall log.\n", [("NEXT", "The shop shall log.", 3)], ["no sentence"]),
        ("## Overview\ntext\n", [], ["not an intent ID"]),
        ("```\n## CAP\n```\n### CAP\nprose\n", [], []),
        ("## CAP\nby: charge\n", [], ["no sentence"]),
    ],
)
def test_parse(source, decls, problems):
    m = lower_intents_md("intents.md", source)
    assert [(d.id, d.text, d.loc.line) for d in m.intents] == decls
    assert len(m.problems) == len(problems) and all(w in msg for w, (msg, _) in zip(problems, m.problems))


def test_cross_file_intent_is_backed_from_its_scope(tmp_path):
    tree(tmp_path, {"intents.md": md(("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")})
    _, got = report(tmp_path)
    pay = got["PAY"]
    assert (pay.status, pay.pointers, pay.advice, pay.scope, pay.loc) == ("backed", [], [], "", ("intents.md", 5))


@pytest.mark.parametrize(
    "files, pointer, advice",
    [
        ({"a/intents.md": md(("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")}, "b/y.py is outside a/", None),
        ({"a/intents.md": md(("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY") + fn("refund", "PAY")}, None, "every lemma is in a/x.py"),
        ({"intents.md": md(("PAY", SAME, "")), "x.py": f"#@ intent PAY: {SAME}\n\n" + fn("charge", "PAY")}, "declared more than once", None),
        ({"x.py": f"#@ intent PAY: {SAME}\n#@ intent PAY: {SAME}\n\n" + fn("charge", "PAY")}, "declared more than once", None),
    ],
)
def test_scope_duplicates_and_sprawl(tmp_path, files, pointer, advice):
    tree(tmp_path, files)
    _, got = report(tmp_path)
    pay = got["PAY"]
    assert any(pointer in p for p in pay.pointers) if pointer else not pay.pointers
    assert any(advice in a for a in pay.advice) if advice else not pay.advice


@pytest.mark.parametrize(
    "files, code",
    [
        ({"intents.md": md(("PAY", SAME, "")), "x.py": fn("charge", None)}, 1),  # orphan in intents.md
        ({"x.py": f"#@ intent PAY: {SAME}\n\n" + fn("charge", None)}, 0),  # unbacked comment
        ({"intents.md": "## pay\nThe shop shall pay.\n", "x.py": fn("charge", None)}, 1),  # malformed file
        ({"intents.md": md(("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")}, 0),
    ],
)
def test_intents_exit_code(tmp_path, capsys, files, code):
    tree(tmp_path, files)
    assert run(tmp_path, capsys=capsys)[0] == code


def test_symlinked_code_is_judged_where_it_lives(tmp_path):
    tree(tmp_path, {"a/intents.md": md(("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")})
    (tmp_path / "a/ld").symlink_to("../b")
    _, got = report(tmp_path, ["a", "a/ld/y.py"])
    assert any("a/ld/y.py is outside a/" in p for p in got["PAY"].pointers)


@pytest.mark.parametrize("cited", [True, False])
def test_partial_check_reports_its_own_intents_md_over_an_ancestor(tmp_path, cited):
    tree(tmp_path, {"intents.md": md(("PAY", SAME, "")), "s/intents.md": md(("PAY", SAME, "")), "s/y.py": fn("refund", "PAY" if cited else None)})
    _, got = report(tmp_path, ["s"])
    pay = got["PAY"]
    assert (pay.loc, pay.scope, pay.status) == (("s/intents.md", 5), "s", "backed" if cited else "unbacked")
    assert any("declared more than once" in p for p in pay.pointers)


def test_checking_one_file_reads_ancestor_intents(tmp_path):
    tree(tmp_path, {"intents.md": md(("PAY", SAME, "charge, refund"), ("ELSE", "The shop shall log.", "")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")})
    _, got = report(tmp_path, ["a/x.py"])
    assert set(got) == {"PAY"}  # uncited ancestor intents are not this check's business
    assert got["PAY"].status == "backed" and not got["PAY"].pointers and not got["PAY"].advice


@pytest.mark.parametrize(
    "target, expected",
    [
        ("a/x.py", {"PAY": "cited by charge", "AREA": "declared in a/intents.md", "LOCAL": "declared in a/x.py"}),
        ("b/y.py", {"PAY": "by: lists refund"}),
        ("a", {"PAY": "cited by charge", "AREA": "declared in a/intents.md", "LOCAL": "declared in a/x.py"}),
    ],
)
def test_intents_for(tmp_path, target, expected):
    tree(
        tmp_path,
        {
            "intents.md": md(("PAY", SAME, "charge, refund")),
            "a/intents.md": md(("AREA", "The shop shall log.", "")),
            "a/x.py": "#@ intent LOCAL: The shop shall count.\n\n" + fn("charge", "PAY"),
            "b/y.py": fn("refund", None),
        },
    )
    got = {x["id"]: x["why"] for x in intents_for(str(tmp_path / target), [str(tmp_path)], str(tmp_path))}
    assert set(got) == set(expected) and all(w in got[k] for k, w in expected.items())


def test_json_and_ledger_carry_the_declaring_file(tmp_path, capsys):
    tree(tmp_path, {"intents.md": md(("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")})
    _, out = run(tmp_path, "--json", capsys=capsys)
    (pay,) = json.loads(out)
    assert (pay["at"], pay["scope"]) == ("intents.md:5", "")
    from telic.ledger import snapshot

    rep, _ = report(tmp_path)
    ledger = snapshot(rep)
    assert ledger["intents"]["PAY"]["declared"] == "intents.md"
    assert affected_files(str(tmp_path), {"intents.md"}, ledger) == {"intents.md", "a/x.py", "b/y.py"}


@pytest.mark.parametrize("args", [["check", "{root}/nope.py"], ["intents", "--for", "{root}/deep/nope.py"], ["{root}/nope"]])
def test_missing_path_is_one_line_error(tmp_path, capsys, args):
    assert main([a.format(root=tmp_path) for a in args]) == 2
    err = capsys.readouterr().err.strip()
    assert "nope" in err and "no such file" in err and "\n" not in err
