# Working on telic

telic is a static verifier: frontends lower Python/TypeScript/Rust plus
`@`-comment contracts into one IR; `vcgen.py` (or the OxCaml engine in
`core/`) turns each function into proof obligations; Z3 and Lean discharge
them; counterexamples are replayed in the real runtime. Read
[docs/design.md](docs/design.md) first, and [docs/handoff.md](docs/handoff.md)
for the known gaps.

## Map

| path | owns |
|---|---|
| `telic/ir.py` | the IR. Language differences are distinct operators, never shared names |
| `telic/contracts.py` | `@`-comment grammar shared by all frontends |
| `telic/frontend/python.py`, `telic/frontend/ts/lower.mjs`, `telic/frontend/rust.py` | lowering; what can't be modelled exactly becomes opaque (with its assumption recorded) or `Unsupported(reason)` |
| `telic/logic.py` | VC terms, smart constructors, theory definitions and lemmas |
| `telic/vcgen.py` | symbolic execution → `Obligation`s; pure functions → definitions |
| `telic/infer.py` | Houdini invariants, loop variants, recursion measures |
| `telic/smt.py`, `telic/lean.py` | backends; Lean sidecars, agent loop, axiom audit |
| `telic/replay.py`, `telic/replay_harness.py`, `telic/frontend/ts/harness.mjs`, `telic/frontend/rust_replay.py` | executing counterexamples, fuzzing, shrinking |
| `telic/equiv.py`, `telic/gaps.py` | `@mirrors` and spec-gap mutation |
| `telic/checker.py`, `telic/render.py`, `telic/cli.py` | pipeline, receipts (obligation + function level, bound to the toolchain), output |
| `telic/ledger.py` | `telic.ledger.json`, the CI ratchet, exact affected-file scope, `telic init` |
| `telic/intent.py` | intents: EARS lint, two-sided `by:` links, backed/broken status, reviews and judgments |
| `telic/propose.py`, `telic/phrase.py` | `telic propose`: proved facts, crash-free preconditions, facts rendered as EARS drafts |
| `telic/oracle.py` | the only place a judgment is delegated to a model: typed questions, pluggable backends (builtin, Jev, HTTP, command, Python, LLM), cache. Answers are labelled, never proof |
| `core/`, `telic/engine.py`, `telic/irjson.py` | the native engine (OxCaml): VC generation + parallel solving, `--engine ox` / `TELIC_ENGINE=ox`; covers everything the Python core models (heap, optionals, dicts, opaque values, try, async); a function it cannot handle falls back to the Python core. `tests/test_engine.py` compares it with the Python core obligation by obligation |
| `telic/lean/Theory.lean` | Lean proofs of every theory lemma Z3 is given |

## Rules

- **Soundness first.** A change that can make telic report `proved` for a false
  claim is a bug, whatever else it fixes. When a construct can't be modelled
  exactly, make it opaque with a conservative effect and record the assumption
  (`VCGen.note`), or reject it with a reason and a line. Add an exploit to
  `tests/cases/soundness/` for every such case.
- **New semantics need differential tests.** Any operator or builtin you add to a
  frontend gets cases in `tests/test_semantics.py`, compared against the real
  interpreter.
- **New theory lemmas need Lean proofs** in `telic/lean/Theory.lean` under the
  same name (`tests/test_lean.py` enforces this).
- **Verdict changes go through the corpora.** `tests/cases/corpus.py`,
  `corpus.ts` and `corpus.rs` pin the expected verdict of every function; add a
  case for every bug you fix.
- **Models only through `oracle.py`.** Ask typed questions (noul / choice /
  score) with a builtin rule as the fallback; `text` questions are optional
  extras a System One classifier won't answer. Never let an answer change a
  proof verdict. Credentials come from the environment and never go in the repo.
- **Output is product.** Messages are one line, source-anchored, and say what to
  do next. Keep success quiet.

## Checks

```bash
pip install -e '.[test]'
pytest -q                           # Lean tests skip if Lean is not installed
telic demo --no-pause               # the end-to-end story must stay green
make -C core                        # native engine; needs an OxCaml switch (5.2.0+ox)
```
