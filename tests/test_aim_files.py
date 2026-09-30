"""aims/<ID>.md: cross-file aims scoped to a directory, one ID space with
comments, found by `telic aims --for`, and carried into the ledger."""

import json
from pathlib import Path

import pytest

from telic.checker import CheckOptions, check
from telic.cli import main
from telic.frontend.aim_file import lower_aim_file
from telic.aim import aims_for
from telic.ledger import affected_files

SAME = "WHEN a charge is made, the shop shall charge a non-negative amount."


def fn(name: str, iid: str | None) -> str:
    cite = f"    #@ aim {iid}\n" if iid else ""
    return f"def {name}(x: int) -> int:\n    #@ requires x >= 0\n{cite}    #@ ensures result >= 0\n    return x\n\n\n"


def tree(root: Path, files: dict[str, str]) -> Path:
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return root


def aims(where: str, *decls: tuple[str, str, str]) -> dict[str, str]:
    return {f"{where}aims/{i}.md": f"{s}\n" + (f"by: {b}\n" if b else "") for i, s, b in decls}


def report(root: Path, paths=(".",)):
    rep = check([str(root / p) for p in paths], CheckOptions(cache_path=None, lean=False, replay=False), root=str(root))
    return rep, {i.id: i for i in rep.aims}


def run(root: Path, *args: str, capsys=None) -> tuple[int, str]:
    code = main(["aims", *args, "--root", str(root), "--no-cache", "--no-lean", "--no-replay"] + [str(root)] * (not any(a.startswith("--for") for a in args)))
    return code, capsys.readouterr().out if capsys else ""


@pytest.mark.parametrize(
    "name, source, decls, problems",
    [
        ("CAP", f"{SAME}\nby: a, b.c\n", [("CAP", f"{SAME} by: a, b.c", 1)], []),
        ("CAP", "\nWHEN a charge is made,\nthe shop shall charge.\n", [("CAP", "WHEN a charge is made, the shop shall charge.", 2)], []),
        ("CAP", "by: charge\n", [], ["no sentence"]),
        ("CAP", "", [], ["no sentence"]),
        ("CAP", f"## CAP\n{SAME}\n", [], ["has a heading"]),
        ("cap", f"{SAME}\n", [], ["not an aim ID"]),
        ("CAP_2", f"{SAME}\n", [], ["not an aim ID"]),
    ],
)
def test_parse(name, source, decls, problems):
    m = lower_aim_file(f"x/aims/{name}.md", source)
    assert [(d.id, d.text, d.loc.line) for d in m.aims] == decls
    assert len(m.problems) == len(problems) and all(w in msg for w, (msg, _) in zip(problems, m.problems))


def test_cross_file_aim_is_backed_from_its_scope(tmp_path):
    tree(tmp_path, {**aims("", ("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")})
    _, got = report(tmp_path)
    pay = got["PAY"]
    assert (pay.status, pay.pointers, pay.advice, pay.scope, pay.loc) == ("backed", [], [], "", ("aims/PAY.md", 1))


@pytest.mark.parametrize(
    "files, pointer, advice",
    [
        ({**aims("a/", ("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")}, "b/y.py is outside a/", None),
        ({**aims("a/", ("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY") + fn("refund", "PAY")}, None, "every lemma is in a/x.py"),
        ({**aims("", ("PAY", SAME, "")), "x.py": f"#@ aim PAY: {SAME}\n\n" + fn("charge", "PAY")}, "declared more than once", None),
        ({"x.py": f"#@ aim PAY: {SAME}\n#@ aim PAY: {SAME}\n\n" + fn("charge", "PAY")}, "declared more than once", None),
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
        ({**aims("", ("PAY", SAME, "")), "x.py": fn("charge", None)}, 1),  # orphan aim file
        ({"x.py": f"#@ aim PAY: {SAME}\n\n" + fn("charge", None)}, 0),  # unbacked comment
        ({"aims/pay.md": "The shop shall pay.\n", "x.py": fn("charge", None)}, 1),  # bad filename
        ({**aims("", ("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")}, 0),
    ],
)
def test_aims_exit_code(tmp_path, capsys, files, code):
    tree(tmp_path, files)
    assert run(tmp_path, capsys=capsys)[0] == code


def test_symlinked_code_is_judged_where_it_lives(tmp_path):
    tree(tmp_path, {**aims("a/", ("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")})
    (tmp_path / "a/ld").symlink_to("../b")
    _, got = report(tmp_path, ["a", "a/ld/y.py"])
    assert any("a/ld/y.py is outside a/" in p for p in got["PAY"].pointers)


@pytest.mark.parametrize("cited", [True, False])
def test_partial_check_reports_its_own_aims_md_over_an_ancestor(tmp_path, cited):
    tree(tmp_path, {**aims("", ("PAY", SAME, "")), **aims("s/", ("PAY", SAME, "")), "s/y.py": fn("refund", "PAY" if cited else None)})
    _, got = report(tmp_path, ["s"])
    pay = got["PAY"]
    assert (pay.loc, pay.scope, pay.status) == (("s/aims/PAY.md", 1), "s", "backed" if cited else "unbacked")
    assert any("declared more than once" in p for p in pay.pointers)


def test_checking_one_file_reads_ancestor_aims(tmp_path):
    tree(tmp_path, {**aims("", ("PAY", SAME, "charge, refund"), ("ELSE", "The shop shall log.", "")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")})
    _, got = report(tmp_path, ["a/x.py"])
    assert set(got) == {"PAY"}  # uncited ancestor aims are not this check's business
    assert got["PAY"].status == "backed" and not got["PAY"].pointers and not got["PAY"].advice


def test_a_deep_check_reads_every_aims_dir_above_it(tmp_path):
    tree(tmp_path, {**aims("", ("TOP", SAME, "")), **aims("a/", ("MID", SAME, "")), **aims("a/b/c/", ("LOW", SAME, "")), "a/b/c/x.py": fn("f", "TOP") + fn("g", "MID") + fn("h", "LOW")})
    _, got = report(tmp_path, ["a/b/c/x.py"])
    assert {k: (i.status, i.loc[0]) for k, i in got.items()} == {"TOP": ("backed", "aims/TOP.md"), "MID": ("backed", "a/aims/MID.md"), "LOW": ("backed", "a/b/c/aims/LOW.md")}

@pytest.mark.parametrize("name", ["README.md", "readme.md", "ReadMe.md"])
@pytest.mark.parametrize("check", [".", "a/x.py"])
def test_readme_in_aims_is_a_doc(tmp_path, capsys, name, check):
    tree(tmp_path, {**aims("", ("PAY", SAME, "")), f"aims/{name}": "# Aims\n\nOne file per aim.\n", "a/x.py": fn("charge", "PAY")})
    rep, got = report(tmp_path, [check])
    assert set(got) == {"PAY"} and not any(m.problems for m in rep.modules)
    assert run(tmp_path, capsys=capsys)[0] == 0

@pytest.mark.parametrize(
    "target, expected",
    [
        ("a/x.py", {"PAY": "cited by charge", "AREA": "declared in a/aims/AREA.md", "LOCAL": "declared in a/x.py"}),
        ("b/y.py", {"PAY": "by: lists refund"}),
        ("a", {"PAY": "cited by charge", "AREA": "declared in a/aims/AREA.md", "LOCAL": "declared in a/x.py"}),
    ],
)
def test_aims_for(tmp_path, target, expected):
    tree(
        tmp_path,
        {
            **aims("", ("PAY", SAME, "charge, refund")),
            **aims("a/", ("AREA", "The shop shall log.", "")),
            "a/x.py": "#@ aim LOCAL: The shop shall count.\n\n" + fn("charge", "PAY"),
            "b/y.py": fn("refund", None),
        },
    )
    got = {x["id"]: x["why"] for x in aims_for(str(tmp_path / target), [str(tmp_path)], str(tmp_path))}
    assert set(got) == set(expected) and all(w in got[k] for k, w in expected.items())


def test_json_and_ledger_carry_the_declaring_file(tmp_path, capsys):
    tree(tmp_path, {**aims("", ("PAY", SAME, "charge, refund")), "a/x.py": fn("charge", "PAY"), "b/y.py": fn("refund", "PAY")})
    _, out = run(tmp_path, "--json", capsys=capsys)
    (pay,) = json.loads(out)
    assert (pay["at"], pay["scope"]) == ("aims/PAY.md:1", "")
    from telic.ledger import snapshot

    rep, _ = report(tmp_path)
    ledger = snapshot(rep)
    assert ledger["aims"]["PAY"]["declared"] == "aims/PAY.md"
    assert affected_files(str(tmp_path), {"aims/PAY.md"}, ledger) == {"aims/PAY.md", "a/x.py", "b/y.py"}


@pytest.mark.parametrize("args", [["check", "{root}/nope.py"], ["aims", "--for", "{root}/deep/nope.py"], ["{root}/nope"]])
def test_missing_path_is_one_line_error(tmp_path, capsys, args):
    assert main([a.format(root=tmp_path) for a in args]) == 2
    err = capsys.readouterr().err.strip()
    assert "nope" in err and "no such file" in err and "\n" not in err


@pytest.mark.parametrize("paths", [["."], ["a"], ["a/x.py"]])
def test_a_symlinked_aims_dir_is_read_once_from_every_check(tmp_path, paths):
    tree(tmp_path, {"shared/PAY.md": f"{SAME}\n", "a/x.py": fn("charge", "PAY")})
    (tmp_path / "aims").symlink_to("shared")
    (tmp_path / "a/aims").symlink_to("../shared")
    _, got = report(tmp_path, paths)
    assert (got["PAY"].status, got["PAY"].loc, got["PAY"].pointers) == ("backed", ("aims/PAY.md", 1), [])


@pytest.mark.parametrize(
    "stray, named",
    [
        ("aims/OTHER.MD", "file 'OTHER.MD'"),
        ("aims/PAY.txt", "file 'PAY.txt'"),
        ("aims/notes", "file 'notes'"),
        ("aims/sub/OTHER.md", "directory 'sub'"),
        ("aims/sub/aims/OTHER.md", "directory 'sub'"),
        ("aims/OTHER.md/x", "directory 'OTHER.md'"),
        ("aims/.DS_Store", None),
    ],
)
@pytest.mark.parametrize("check", [".", "a/x.py", "aims"])
def test_anything_else_in_aims_is_an_error_naming_it(tmp_path, capsys, stray, named, check):
    tree(tmp_path, {**aims("", ("PAY", SAME, "")), stray: f"{SAME}\n", "a/x.py": fn("charge", "PAY")})
    rep, got = report(tmp_path, [check])
    problems = [msg for m in rep.modules for msg, _ in m.problems]
    assert got["PAY"].status == ("unbacked" if check == "aims" else "backed")
    assert (len(problems), all(named in p for p in problems)) == ((1, True) if named else (0, True))
    assert run(tmp_path, capsys=capsys)[0] == (1 if named else 0)
