"""`telic demo`: a narrated, fully real walk through telic.

Every command below runs for real on real files in a scratch workspace; the
edits between steps are the ones an agent would make. Nothing is canned.
"""

from __future__ import annotations

import contextlib
import io
import os
import shutil
import sys
import tempfile
import textwrap
from dataclasses import dataclass, field
from pathlib import Path

SCENARIO = Path(__file__).resolve().parent / "scenario"


@dataclass
class Step:
    say: str
    run: list[str] | None = None
    edits: list[tuple[str, str, str]] = field(default_factory=list)  # (file, old, new)
    show: tuple[str, int, int] | None = None  # (file, first line, last line)
    title: str | None = None


ACTS: list[Step] = [
    Step(
        title="telic",
        say="""
        A small shop, vibecoded overnight: billing rules in Python, the checkout
        page in TypeScript, zero tests. What it does have is its aims, written down
        where the code lives, and contracts in comments. The runtime never
        executes a comment, so they cost nothing in production.
        """,
        show=("server/billing.py", 5, 26),
    ),
    # -- Act 1 -------------------------------------------------------------
    Step(
        title="ACT 1 · The comment that found the bug",
        say="""
        Check the server. telic turns every function and its contract into proof
        obligations and hands them to an SMT solver. It needs no test inputs and
        runs nothing yet.
        """,
        run=["check", "server/billing.py"],
    ),
    Step(
        say="""
        That counterexample came out of the comment, not a test. telic then ran the
        real function on those exact inputs to confirm it: this is a bug, not a
        solver artifact. order_total proved too, and nobody wrote its loop
        invariant: telic inferred `total >= 0` and proved that as well.

        The agent fixes the bug.
        """,
        edits=[("server/billing.py", "    if requested > paid:\n", "    if requested > paid - refunded:\n")],
        run=["check", "server/billing.py"],
    ),
    Step(
        say="""
        Proved. But proved against *what*? A proof is only as good as the contract.
        telic gaps attacks the contract itself: it makes small, plausible mistakes
        in the proved code and re-verifies each one against the unchanged contract.
        """,
        run=["gaps", "server/billing.py", "--only", "refund_amount"],
    ),
    Step(
        say="""
        The contract happily accepts "always refund zero." Both mutants pass every
        proof obligation, yet on the inputs shown they return different amounts.
        Say what you mean:
        """,
        edits=[
            (
                "server/billing.py",
                "    #@ ensures 0 <= result <= paid - refunded\n",
                "    #@ ensures 0 <= result <= paid - refunded\n    #@ ensures result == min(requested, paid - refunded)\n",
            )
        ],
        run=["gaps", "server/billing.py", "--only", "refund_amount"],
    ),
    # -- Act 2 -------------------------------------------------------------
    Step(
        title="ACT 2 · Your frontend and your backend disagree",
        say="""
        The checkout page re-implements the discount in TypeScript. That
        requirement spans the server and the page, so it is declared in the
        aims/ directory at the top of the shop, whose scope is everything
        below it. The filename is the ID.
        """,
        show=("aims/PRICE-AGREE.md", 1, 3),
    ),
    Step(
        say="""
        The page declares that it mirrors the server. Both functions meet their
        own contracts. Do they agree with each other?
        """,
        show=("web/checkout.ts", 3, 10),
        run=["check", "web/checkout.ts"],
    ),
    Step(
        say="""
        Same inputs, one cent apart, and telic proved it: it lowered both languages
        into one logic, where Python's round() and JavaScript's Math.round() are
        different operators, found the input, then ran Python and Node to confirm.
        The customer sees 7 and the card is charged 8.

        The agent moves both sides to integer arithmetic.
        """,
        edits=[
            ("server/billing.py", "return subtotal - round(subtotal * percent / 100)", "return subtotal - (subtotal * percent + 50) // 100"),
            ("web/checkout.ts", "return subtotal - Math.round((subtotal * percent) / 100);", "return subtotal - Math.floor((subtotal * percent + 50) / 100);"),
        ],
        run=["check", "web/checkout.ts"],
    ),
    # -- Act 3 -------------------------------------------------------------
    Step(
        title="ACT 3 · When the solver gives up, Lean takes over",
        say="""
        Some truths need induction, and SMT solvers can't do induction. Without Lean,
        telic says so honestly instead of guessing:
        """,
        show=("server/referrals.py", 6, 20),
        run=["check", "server/referrals.py", "--no-lean", "--timeout", "2"],
    ),
    Step(
        say="""
        telic renders the exact obligation as a Lean 4 theorem, with the code
        translated into Lean definitions, an unfolding lemma per definition, and
        callee contracts as explicit hypotheses:
        """,
        run=["lean", "chained_bonus_is_product/ensures@20>21", "server/referrals.py", "--timeout", "2"],
    ),
    Step(
        say="""
        An agent wrote the proof (`telic prove --agent "claude -p"`); it lives next to
        the code in referrals.py.proof.lean. telic accepts it only if the Lean
        kernel checks it and #print axioms shows nothing beyond Lean's standard
        three: no sorry, no native_decide, no smuggled axioms.
        """,
        run=["check", "server/referrals.py", "--timeout", "2"],
    ),
    Step(
        say="""
        Proofs are tied to the code they are about. Change the code and telic
        regenerates the theorem; a proof that no longer matches is stale, and only
        that proof. Nothing is silently trusted:
        """,
        edits=[("server/referrals.py", "return level_bonus(a + b) == level_bonus(a) * level_bonus(b)", "return level_bonus(b + a) == level_bonus(a) * level_bonus(b)")],
        run=["check", "server/referrals.py", "--timeout", "2"],
    ),
    Step(
        title="the whole shop",
        say="""
        Put the proof back and check everything. Every aim is backed but one, and
        telic says why: "never a negative total" is also met by `return 0`. A
        prohibition needs a lemma that says what the code still does, or an
        empty function satisfies it.
        """,
        edits=[("server/referrals.py", "return level_bonus(b + a) == level_bonus(a) * level_bonus(b)", "return level_bonus(a + b) == level_bonus(a) * level_bonus(b)")],
        run=["check", ".", "--timeout", "2"],
    ),
]


# ---------------------------------------------------------------------------


class Out:
    def __init__(self, color: bool):
        self.color = color

    def c(self, code: str, s: str) -> str:
        return f"\033[{code}m{s}\033[0m" if self.color else s


def _width() -> int:
    try:
        return min(100, os.get_terminal_size().columns)
    except OSError:
        return 88


def show_file(o: Out, root: Path, rel: str, lo: int, hi: int) -> str:
    lines = (root / rel).read_text().splitlines()
    out = [o.c("2", f"  {rel}")]
    for i in range(lo, min(hi, len(lines)) + 1):
        text = lines[i - 1]
        if ("@" in text and text.lstrip().startswith(("#@", "//@"))) or (rel.endswith(".md") and text.startswith("## ")):
            text = o.c("36", text)
        out.append(o.c("2", f"  {i:>3} │ ") + text)
    return "\n".join(out)


def run_demo(pause: bool | None = None, color: bool | None = None, workspace: str | None = None, keep: bool = False) -> int:
    from ..cli import main as telic_main

    color = sys.stdout.isatty() if color is None else color
    pause = sys.stdin.isatty() and sys.stdout.isatty() if pause is None else pause
    o = Out(color)
    ws = Path(workspace) if workspace else Path(tempfile.mkdtemp(prefix="telic-demo-"))
    if ws.exists() and any(ws.iterdir()):
        shutil.rmtree(ws)
    shutil.copytree(SCENARIO, ws, dirs_exist_ok=True)
    width = _width()
    cwd = os.getcwd()
    os.chdir(ws)
    if color:
        os.environ["FORCE_COLOR"] = "1"
    else:
        os.environ["NO_COLOR"] = "1"  # wins over a FORCE_COLOR the environment sets
    try:
        for i, step in enumerate(ACTS):
            if step.title:
                bar = f"━━ {step.title} "
                print()
                print(o.c("1;35", bar + "━" * max(3, width - len(bar))))
            print()
            for para in textwrap.dedent(step.say).strip().split("\n\n"):
                print(textwrap.fill(" ".join(para.split()), width=min(width, 84), initial_indent="  ", subsequent_indent="  "))
                print()
            for rel, old, new in step.edits:
                p = ws / rel
                text = p.read_text()
                if old not in text:
                    raise SystemExit(f"demo edit failed: {old!r} not in {rel}")
                p.write_text(text.replace(old, new, 1))
                print(o.c("2", f"  ✎ edited {rel}"))
                for l_old, l_new in zip(old.rstrip("\n").split("\n"), new.rstrip("\n").split("\n")):
                    if l_old != l_new:
                        print(o.c("31", f"    - {l_old.strip()}"))
                        print(o.c("32", f"    + {l_new.strip()}"))
                for extra in new.rstrip("\n").split("\n")[len(old.rstrip(chr(10)).split(chr(10))):]:
                    print(o.c("32", f"    + {extra.strip()}"))
                print()
            if step.show:
                print(show_file(o, ws, *step.show))
                print()
            if step.run:
                shown = " ".join(a if " " not in a else repr(a) for a in step.run)
                print(o.c("1", f"  $ telic {shown}"))
                print()
                buf = io.StringIO()
                with contextlib.redirect_stdout(buf):
                    try:
                        telic_main(list(step.run) + (["--color", "always"] if color and step.run[0] == "check" else []))
                    except SystemExit:
                        pass
                for line in buf.getvalue().rstrip().splitlines():
                    print("  " + line)
                print()
            if pause and i < len(ACTS) - 1:
                try:
                    input(o.c("2", "  ⏎ "))
                except EOFError:
                    pass
    finally:
        os.chdir(cwd)
        if not keep and not workspace:
            shutil.rmtree(ws, ignore_errors=True)
    print(o.c("2", f"  workspace: {ws}" if keep or workspace else "  (scratch workspace removed; run `telic demo --keep` to explore it)"))
    return 0


def add_commands(sub) -> None:
    d = sub.add_parser("demo", help="a narrated, fully real walk through telic")
    d.add_argument("--no-pause", action="store_true", help="do not wait for Enter between steps")
    d.add_argument("--keep", action="store_true", help="keep the scratch workspace")
    d.add_argument("--workspace", help="run in this directory (it will be overwritten)")
    d.add_argument("--color", choices=["auto", "always", "never"], default="auto")
    d.set_defaults(func=lambda a: run_demo(pause=False if a.no_pause else None, color=True if a.color == "always" else False if a.color == "never" else None, workspace=a.workspace, keep=a.keep))
