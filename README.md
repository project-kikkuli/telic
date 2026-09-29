# telic

**Write what your code promises in a comment. telic proves it, or shows you the input that breaks it, after running your code on that input.**

Python, TypeScript and Rust. The contracts are comments, so production code pays nothing for them.

```python
def discount(total: int, code: str | None, codes: dict[str, int]) -> int:
    #@ requires total >= 0
    #@ ensures 0 <= result <= total
    if code is None or code not in codes:
        return total
    return total - total * codes[code] // 100
```

```
$ telic check shop.py

✗ REFUTED discount · postcondition can be false ──────────────────── shop.py:6
     │
   3 │     #@ ensures 0 <= result <= total
     │                ━━━━━━━━━━━━━━━━━━━━ can be false
     ┆
   6 │     return total - total * codes[code] // 100
     │     ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ when it returns here
     │
   counterexample  discount(total=1, code='', codes={'': -1})
   replayed        ✓ python: returned 2; '0 <= result <= total' is false
```

Nobody wrote a test. telic took the counterexample from the solver, ran the real function on it, and it failed. A negative discount code raises the price.

## Use it

```bash
pip install -e .        # Python ≥ 3.10. TypeScript also needs Node ≥ 18;
                        # Rust needs pip install -e '.[rust]' (and rustc to replay)
telic demo              # 20-second walkthrough on a small shop
telic check src/        # check a project
```

Then follow this loop, or have your coding agent follow it:

1. **Say what a function promises.** Add `#@ requires` (what callers guarantee) and
   `#@ ensures` (what it returns; `result` is the return value, `old(x)` is x at
   entry). In TypeScript and Rust, write `//@`.
2. **Run `telic check`.** Each promise, and each place the code could crash, is
   either proved or comes back with a counterexample telic has actually executed.
3. **Fix the code or the contract.** telic says which one disagrees and where.
4. **Keep it proved.** `telic init` adds a CI check that fails when anything
   that was proved stops being proved.

## What it catches

| | how it shows up |
|---|---|
| broken promises | `✗ REFUTED` with an executed counterexample, as above |
| crashes | `None` where a value is needed, missing dict key, index out of range, division by zero, an unintended `raise`; each one proved impossible or reproduced |
| races | `⚡ RACE`: state checked before an `await` and used after it, when another task can change it in between |
| frontend/backend drift | `//@ mirrors ../server/billing.py::discounted_total`: the two must agree on every input, or telic shows the input where they don't (e.g. banker's rounding vs `Math.round`) |
| contracts that say too little | `telic gaps` mutates proved code; a mutant the contract still accepts is a bug the contract would let through |

It works on ordinary code: classes, optionals, dicts/Maps, enums, pydantic
models, async, try/except, comprehensions, imports between your files. Anything
it can't model (a library call, an untyped value) becomes opaque: nothing is
assumed about its result, and what telic does assume (for example "`requests.get`
does not raise") is listed under **trusted base** in every report. On real
libraries it models 87–92% of functions.

## Intents: requirements above proofs

An intent is a requirement a reviewer can read: one sentence, in
[EARS](https://alistairmavin.com/ears/) form. The contracts that back it can sit
anywhere in the project, in either language.

```python
#@ intent REFUND-CAP: WHEN a refund is requested, the shop shall refund at most
#@   what the customer paid, net of earlier refunds.
#@   by: refund_amount, web/checkout.ts::refundButton

def refund_amount(paid: int, refunded: int, requested: int) -> int:
    #@ intent REFUND-CAP
    #@ ensures 0 <= result <= paid - refunded
    ...
```

`by:` points down from the requirement to its lemmas, and each lemma cites the
intent back. telic checks both directions. An intent is **backed** when every
lemma is proved, and **broken** when one is refuted. It is never "proved": whether
the lemmas cover the requirement is a separate verdict, recorded by a person
(`telic intents --accept ID`) or by a cheap model (`--judge`). Both are pinned to
the exact sentence and lemma set.

**Starting from code with no contracts,** `telic propose src/` lists facts it
has proved about the code as it is (a proposed contract is only shown once it
is proved) and the preconditions that would make each crashing function
crash-free. With `--intents`, the cheap model drafts EARS requirements from
them. A fact can faithfully describe a bug, and a requirement is a decision, so
you (or your agent) choose what to keep; `--write` inserts the facts.

## When the solver can't decide

Z3 can't do induction. telic turns the stuck obligation into a Lean 4 theorem, and
an agent can prove it: `telic prove --agent "claude -p"`. The Lean kernel checks
the proof, and `#print axioms` rules out `sorry` and any smuggled axiom. The
proof is saved next to the code and reused until the code it's about changes.

## Commands

```
telic check [PATHS]        verify (-j N workers, --json for agents and CI)
telic intents              requirements, their lemmas, and whether the links hold
telic propose [PATHS]      proved facts and crash-free preconditions to adopt; --intents drafts requirements
telic gaps [PATHS]         mutants the contracts fail to reject
telic explain NAME         every obligation of a function, with formulas
telic lean ID / prove      Lean escalation
telic init / ci / ledger   the CI ratchet (telic.ledger.json)
telic report -o out.html   the proof ledger as a page
telic run script.py        run with every contract checked at runtime
```

## What you are trusting

- **Language models.** Python ints are exact; Rust integers are their fixed
  width, and overflow is a panic (debug semantics). Floats and JavaScript
  numbers are exact rationals: no rounding, NaN or Infinity.
- **Z3 and the Lean kernel.**
- **The theory lemmas about sums and counts.** They are proved in
  [Theory.lean](telic/lean/Theory.lean).
- **The verifier's own code.** An adversarial suite of programs built to fool
  telic keeps it honest (`tests/cases/soundness/`).
- **Anything listed under trusted base,** plus anything you mark `@assume` or
  `@trusted`.

Counterexamples need no trust: each one is executed before it's reported.

**Docs:** [contracts](docs/contracts.md) · [how it works](docs/design.md) · [CI](docs/ci.md) · [agents](docs/agents.md) · MIT
