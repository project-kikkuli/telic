# telic

**Contracts in comments. Proofs instead of vibes.**

telic is a static verifier for Python and TypeScript. You (or your coding agent)
write down what the code is *for* as intents, and what each function promises
as contracts in comments, in the style of C0. telic then proves every promise, or
hands you a counterexample it has **actually executed**. It attacks your
contracts to find what they fail to say, proves that your frontend and backend
agree, and when the SMT solver gives up it hands the exact theorem to Lean, where
an agent can write the proof and the kernel checks it.

Comments cost nothing at runtime, so production pays nothing for any of this.

```python
#@ intent REFUND-CAP: A refund never exceeds what the customer paid, net of earlier refunds.

def refund_amount(paid: int, refunded: int, requested: int) -> int:
    #@ requires 0 <= refunded <= paid
    #@ requires requested >= 0
    #@ intent REFUND-CAP
    #@ ensures 0 <= result <= paid - refunded
    if requested > paid:
        return paid - refunded
    return requested
```

```
$ telic check server/billing.py

✗ REFUTED refund_amount · postcondition can be false ──────────── server/billing.py:24
   REFUND-CAP  A refund never exceeds what the customer paid, net of earlier refunds.

      │
   21 │     #@ ensures 0 <= result <= paid - refunded
      │                ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ can be false
      ┆
   24 │     return requested
      │     ━━━━━━━━━━━━━━━━ when it returns here
      │
   counterexample  refund_amount(paid=1, refunded=1, requested=1)
   replayed        ✓ python: returned 1; '0 <= result <= paid - refunded' is false
```

No test was written. The counterexample came from the comment, and telic ran the
real function on it before reporting it.

## Try it

```bash
pip install -e .          # Python ≥ 3.10; installs z3-solver
telic demo                # a narrated, fully real walkthrough (~20 s)
```

TypeScript support needs Node ≥ 18 (the `typescript` package installs itself on
first use). Lean is optional: without it telic stops at "unknown" and says so.
With a Lean 4 toolchain on `PATH` (or `TELIC_LEAN=/path/to/lean`), unknowns
escalate automatically.

## Two things it does that tests can't

**1. It finds the bug from the contract alone and proves it's real.** Every
function becomes a set of proof obligations: each postcondition at each `return`,
each callee precondition at each call, each loop invariant, termination, every
division and every list index. Z3 either proves an obligation or produces a
model. The model is then *replayed*: telic executes the real function, in the
real runtime, with contracts enforced. A counterexample is reported as a bug only
if the program actually misbehaves. If it doesn't, the solver found an unreachable
state, which means a loop invariant is too weak, and telic says exactly that. It
also fuzzes for a real failing input and shrinks it (`weird_inv(4)`, not
`weird_inv(267)`).

**2. It proves that your frontend and backend agree, or shows the input where
they don't.** Business rules get written twice. A TypeScript function that
declares `//@ mirrors ../server/billing.py::discounted_total` must return the
same result as the Python function for every input both accept:

```
✗ DIVERGES discounted_total ≡ displayTotal ─────── server/billing.py ⇄ web/checkout.ts
   PRICE-AGREE  The checkout page shows exactly the amount the server charges.

   input              subtotal=10, percent=25
   server/billing.py  discounted_total(...) → 8
   web/checkout.ts    displayTotal(...) → 7
   replayed           ✓ ran both: python returned 8, typescript returned 7
   why                Python's round() rounds halves to even (banker's rounding); JavaScript's Math.round rounds halves up
                      found by the solver; both functions satisfy their own contracts
```

Both functions pass their own contracts. Both lower into one logic in which
Python's `round` and JavaScript's `Math.round` are different operators, and Z3
finds the input where they split. After the fix, telic prints
`✓ EQUIVALENT … proved: equal results for every input both accept`.

## The loop

```
  intent          #@ intent PRICE-AGREE: The checkout page shows exactly what the server charges.
    │  formalized as
  contracts       #@ requires / ensures / invariant / decreases / mirrors   (comments: zero runtime cost)
    │  lowered to one IR, symbolically executed
  obligations     one per return × postcondition, call × precondition, loop, division, index …
    │  discharged by the cheapest sufficient oracle
  evidence        Z3 ─▶ Lean auto-tactics ─▶ Lean proof by an agent ─▶ honest "unknown"
    │  and cross-examined
  confidence      counterexamples replayed · specs attacked by mutants · axioms audited
```

Each intent's status is computed from evidence, not from whether a test exists:

| status | meaning |
|---|---|
| `✓ proved` | every obligation of every linked function is proved (Z3 or Lean), including termination |
| `✗ refuted` | a counterexample was reproduced by running the real code |
| `? open` | something is unproved: undecided, or the solver's model could not be reproduced |
| `○ unformalized` | declared, but no `@ensures` carries it yet. This is the gap between words and code, made visible |
| `! undeclared` | a clause names an intent nobody declared |

## Attack the contract, not just the code

A proof only means as much as its contract. `telic gaps` makes small, plausible
mistakes in a *proved* function (flipped comparisons, off-by-ones, deleted
updates, wrong return values) and re-verifies each mutant against the unchanged
contract. A mutant that still verifies and provably behaves differently is a
wrong program your contract accepts:

```
◌ GAP refund_amount · the contract accepts 2 wrong versions  server/billing.py:16

      │ return 0
   24 -     return requested
   24 +     return 0
   input     paid=1, refunded=0, requested=1
   returns   1 originally, 0 mutated — and both satisfy every @ensures
```

Add `#@ ensures result == min(requested, paid - refunded)` and every mutant dies.

## When the solver gives up

Some truths need induction. Z3 can't do induction, so telic renders the
obligation as a Lean 4 theorem: the code becomes Lean definitions (guarded by
their preconditions, with termination measures), each gets a proved unfolding
lemma, and every contract the proof relies on appears as an explicit hypothesis,
never as an axiom.

```bash
telic lean chained_bonus_is_product/ensures@18>19   # print the theorem
telic prove --agent "claude -p"                      # let an agent prove every open obligation
```

`telic prove` feeds Lean's errors back to the agent until the kernel accepts a
proof, then stores it next to the code (`referrals.py.proof.lean`). A proof counts
only if it checks **and** `#print axioms` shows nothing beyond Lean's standard
three: `sorry`, `native_decide` and smuggled axioms are all rejected. Statements
are regenerated from the code on every run, so when the code changes, exactly the
affected proof is reported stale.

## Writing contracts

Contracts are expressions in the host language, so they read like the code and
can be checked at runtime.

| | Python | TypeScript |
|---|---|---|
| precondition | `#@ requires 0 <= i < len(xs)` | `//@ requires 0 <= i && i < xs.length` |
| postcondition | `#@ ensures result >= 0` | `//@ ensures result >= 0` |
| entry value | `#@ ensures len(xs) == len(old(xs)) + 1` | `//@ ensures xs.length === old(xs.length) + 1` |
| quantifiers | `all(x > 0 for x in xs)`, `any(...)`, `all(... for i in range(n))` | `xs.every(x => x > 0)`, `range(0, n).every(i => ...)` |
| implication | `implies(a, b)` | `implies(a, b)` |
| loop invariant | `#@ invariant t == sum(xs[:i])` above or inside the loop | `//@ invariant ...` |
| termination | `#@ decreases hi - lo` (loop or recursive function) | `//@ decreases hi - lo` |
| intended exceptions | `#@ raises b == 0` | `//@ raises x > 3` |
| static assertion | `#@ assert y >= 0` | `//@ assert y >= 0` |
| intent | `#@ intent ID: sentence` declares, `#@ intent ID` links, `#@ [ID] ensures …` tags one clause | same with `//@` |
| cross-language | `#@ mirrors ../web/price.ts::quote` | `//@ mirrors ../server/price.py::quote` |
| escape hatches | `#@ trusted`, `#@ assume …` (both listed under "trusted base") | same |

Without any annotations, every checked function still gets its safety obligations:
division by zero, list bounds, reachable `raise`/`throw`, falling off the end of a
value-returning function, and termination. Loop invariants such as `0 <= i <=
len(xs)`, `total == sum(xs[:i])` and `len(out) == i`, and termination measures
like `hi - lo + 1`, are **inferred and proved** (Houdini-style), so binary search
verifies with no hand-written invariant at all.

More in [docs/contracts.md](docs/contracts.md).

## Commands

```
telic check [PATHS]      verify; exit 1 on a refutation (--strict: also on anything open)
telic check --json       machine-readable results for agents and CI
telic explain NAME       every obligation of a function, with its formula and inferred invariants
telic gaps [PATHS]       mutants the contracts fail to reject
telic lean ID            the Lean theorem for one obligation
telic prove --agent CMD  close open obligations in Lean with an agent in the loop
telic report -o out.html the proof ledger as a page: intents, mirrors, source with a proof gutter
telic run script.py      run with every contract enforced (C0's -d)
pytest -p telic.pytest_plugin   enforce contracts during your test suite
telic demo               the walkthrough
```

Results are cached by the exact formula of each obligation (`.telic/cache.json`).
Because calls are verified modularly (against callee *contracts*, not bodies),
editing a function body re-verifies only that function. Editing a contract
re-verifies that function and its callers.

## With a coding agent

telic is built to sit between an agent and `git commit`. The agent writes code,
intents and contracts; telic answers with obligations that are precise,
source-anchored, and each carries an executed counterexample, a missing
invariant, or a Lean goal. See [docs/agents.md](docs/agents.md) for the loop and a
drop-in skill for Claude Code.

## What you are trusting

telic is explicit about its trusted base, and prints it (`telic check -v`):

- **The language models.** Python `int` is exact; `float` and JavaScript `number`
  are modelled as exact rationals (no rounding, NaN or Infinity). JS integers are
  assumed to stay within ±2^53, and distinct list arguments are assumed not to
  alias. Integer and rounding semantics are **differentially tested** against
  CPython and Node on random expressions (`tests/test_semantics.py`).
- **Z3 and the Lean kernel.** Lean proofs are audited with `#print axioms`.
- **The theory lemmas** Z3 gets about sums and counts. They are proved in Lean in
  [`telic/lean/Theory.lean`](telic/lean/Theory.lean), and the test suite
  re-checks that file.
- **The frontends and VC generator**, which are ordinary code and have tests.
- Anything marked `@trusted` or `@assume`, listed in every report.

Counterexamples never rely on trust, because each one is executed before it's
reported. Anything outside the modelled subset (dicts, classes, closures, I/O,
async…) is reported as `⊘ unsupported`, with the line and the reason. telic
never guesses.

## Supported today

Top-level functions over `int`/`float`/`bool`/`str`, lists, and immutable records
(frozen dataclasses / NamedTuple; TypeScript interfaces). `if`/`while`/`for`
(range, lists, `enumerate`, counted `for (let i…)`, `for…of`), `break`/`continue`,
`assert`, `raise`/`throw`, tuple assignment, list `append`/`push`/index
assignment, slices, `sum`/`count`/`in`/`includes`/`reduce(+)`, `min`/`max`/`abs`,
the rounding family (`round`, `math.floor`, `Math.round`, `Math.trunc`...), calls
between checked functions (including recursion and list-mutating callees), and pure
functions inside specifications. See [docs/design.md](docs/design.md) for how
it works and what comes next.

## Development

```bash
pip install -e '.[test]'
pytest                       # ~2 min with Lean installed; Lean tests skip without it
```

MIT licensed.
