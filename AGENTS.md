# Working on telic

telic is a static verifier: frontends lower Python/TypeScript plus `@`-comment
contracts into one IR; `vcgen.py` turns each function into proof obligations;
Z3 and Lean discharge them; counterexamples are replayed in the real runtime.
Read [docs/design.md](docs/design.md) first.

## Map

| path | owns |
|---|---|
| `telic/ir.py` | the IR. Language differences are distinct operators, never shared names |
| `telic/contracts.py` | `@`-comment grammar shared by all frontends |
| `telic/frontend/python.py`, `telic/frontend/ts/lower.mjs` | lowering; anything not modelled exactly becomes `Unsupported(reason)` |
| `telic/logic.py` | VC terms, smart constructors, theory definitions and lemmas |
| `telic/vcgen.py` | symbolic execution → `Obligation`s; pure functions → definitions |
| `telic/infer.py` | Houdini invariants, loop variants, recursion measures |
| `telic/smt.py`, `telic/lean.py` | backends; Lean sidecars, agent loop, axiom audit |
| `telic/replay.py`, `telic/replay_harness.py`, `telic/frontend/ts/harness.mjs` | executing counterexamples, fuzzing, shrinking |
| `telic/equiv.py`, `telic/gaps.py` | `@mirrors` and spec-gap mutation |
| `telic/checker.py`, `telic/render.py`, `telic/cli.py` | pipeline, receipts (obligation + function level, bound to the toolchain), output |
| `telic/ledger.py` | `telic.ledger.json`, the CI ratchet, exact affected-file scope, `telic init` |
| `telic/lean/Theory.lean` | Lean proofs of every theory lemma Z3 is given |

## Rules

- **Soundness first.** A change that can make telic report `proved` for a false
  claim is a bug, whatever else it fixes. When a construct can't be modelled
  exactly, reject it with a reason and a line.
- **New semantics need differential tests.** Any operator or builtin you add to a
  frontend gets cases in `tests/test_semantics.py`, compared against the real
  interpreter.
- **New theory lemmas need Lean proofs** in `telic/lean/Theory.lean` under the
  same name (`tests/test_lean.py` enforces this).
- **Verdict changes go through the corpora.** `tests/cases/corpus.py` and
  `corpus.ts` pin the expected verdict of every function; add a case for every
  bug you fix.
- **Output is product.** Messages are one line, source-anchored, and say what to
  do next. Keep success quiet.

## Checks

```bash
pip install -e '.[test]'
pytest -q                           # Lean tests skip if Lean is not installed
telic demo --no-pause               # the end-to-end story must stay green
```
