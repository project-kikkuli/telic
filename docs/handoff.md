# State of the project

What works, what does not, and where unfinished work lives. Commands and
verdict semantics are in [contracts.md](contracts.md); the architecture is in
[design.md](design.md).

## What works

- `telic check` on Python, TypeScript, Rust and Swift: contracts, crash
  freedom, races across `await`, lifecycles, `@mirrors` across languages.
  Every refutation is replayed in the real runtime before it is reported.
- Two cores: the Python core (`telic/vcgen.py`) and the OxCaml engine
  (`core/`, `TELIC_ENGINE=ox`). `tests/test_engine.py` holds them to the same
  obligations and verdicts.
- Lean escalation (`telic lean`, `telic prove --agent`) with an axiom audit;
  every Z3 theory lemma is proved in `telic/lean/Theory.lean`.
- Aims (EARS requirements with two-sided `by:` links), `telic propose`,
  `telic gaps`, the CI ratchet (`telic.ledger.json`) and oracles.
- UI lemmas on web apps through Playwright ([ui.md](ui.md)).
- Numbers: floats and JavaScript numbers are exact rationals on main (no
  rounding, NaN or infinities). IEEE doubles are on `wip/floats`.

## Blockers

- **iOS is unverified.** Xcode is not installed on the dev machine, so the
  iOS adapter (`telic/ui/ios.py`, `telic/ui/sim.py`) has only run against
  `tests/fake_simulator.py`. Once Xcode is installed, run
  `sh scripts/ios_e2e.sh`.

## CI

Principle: telic replaces test batteries with reused proofs. CI for telic
should be `telic ci` over telic's own ledger, the corpus verdict pins, the
soundness exploits and the differential semantics cases, each rerun only when
its inputs change. Goal: 30 seconds when nothing relevant changed.

Now: `.github/workflows/ci.yml` runs 11 parallel jobs over the existing
pytest suite. Each hashes its inputs (every tracked file except `docs/` and
top-level `*.md`, the pins in `.github/constraints.txt`, the runner image
version and the apt z3 version) and skips everything after checkout when a
passing verdict for that hash is in the Actions cache. Latest runs:
`gh run list -R project-kikkuli/telic`.

Open:

- The key is coarse: any code change reruns every job, and the slowest UI
  tests (`test_concurrent_browsers_never_exceed_the_machine_budget`, about
  7 minutes) set the wall time.
- There is no `telic.ledger.json` for telic itself. `telic ledger telic`
  ran over 10 minutes locally without finishing; find the slow functions
  before making `telic ci` the main CI job.
- Tests and the demo run in temporary directories, so telic's obligation
  store (`.telic/`) is not reused across CI runs.

Removed as duplicates or change detectors: the CI `telic demo` step
(`tests/test_cli.py::test_demo_runs_green` runs it) and the exact-string
assertion in `tests/test_phrase.py` (it now checks that each rendering is
valid EARS).

## Unmerged branches

Each is on origin, unverified unless stated.

| branch | state | next step |
|---|---|---|
| `wip/z3-pin` | pins `z3-solver==5.1.0.0` and makes the engine use the wheel's Z3 instead of the apt one; under Z3 5.1 the engine proves `strunits.ts:emojiAfterBmp`, cause unknown | find why 5.1 proves it (compare the obligation with the Python core), then merge |
| `wip/floats` | IEEE doubles: rounding, NaN, infinities, `-0.0`, JS integers exact to 2^53 | run the full suite and the soundness exploits, then merge |
| `wip/seed-runner` | the `by <actions>` UI clause, count-based UI budgets, `examples/ui/run_seeded.py` with 12 seeded bugs (7 caught with the original aims; the 5 misses were spec gaps) and 5 new aims for them | run the seeded bugs against the new aims |
| `wip/dogfood-errors` | loops, calls and literals telic cannot model report a verdict instead of an error, in both cores | run the corpus and engine tests |
| `wip/friction2` | a model with `seqsum` opaque counts as a counterexample when replay agrees; a regex model (`telic/regex.py`) | run the suite; add soundness exploits for the regex model |
| `wip/speed` | a leftover of the CI speed work; its test changes are on main | delete |

## Known gaps

Soundness items come first: they can make telic say `proved` when it
should not.

### Soundness

- **Classes several files define.** `Program.build` qualifies them
  (`Box@a_shapes`, methods `Box@a_shapes.get`) in the defining module and in
  modules that import them (`qualify_classes` in `telic/program.py`); replay
  maps names back with `ir.source_name`. What stays unsupported: a module
  that uses such a name without defining or importing it, or through a
  declaration borrowed from a file that means the other class
  (`Module.ambiguous_classes`). Exceptions are matched by name, not
  qualified: a `raise` of one file's `LowerError` caught as another's is not
  told apart.
- **Vacuity is checked at entry only.** A function whose `@requires` and
  object-parameter invariants are unsatisfiable is `vacuous`
  (`Vacuity` in `telic/checker.py`). Not checked: an `@assume` or a
  `@trusted` callee's `@ensures` that is unsatisfiable only in the
  context of a call; an entry check Z3 cannot decide leaves the verdict
  alone. A trusted function's own contract is checked for satisfiability
  (`VCGen.contract_probe`), unfolding predicates once round their
  recursion group; deeper contradictions are caught in each function
  whose proof unfolds that deep (its unfoldings are checked together,
  `_body_lemmas` in `telic/checker.py`), never in the predicate itself.
- **Callbacks checked on their own lose what the caller knows.** A unit
  (`lambda_unit` in `telic/frontend/python.py`, `unit` in
  `telic/frontend/ts/lower.mjs`, `closure_unit` in `rust.py` and
  `swift_expr.py`) is checked for every argument its types allow. So a Rust
  or Swift closure given to `sort_by_key`/`forEach`, or a statement-bodied TS
  callback, does not see a `@requires` fact about the list's elements. Done
  looks like running those bodies per element in place, as the
  expression-bodied Python and TypeScript callbacks already are. Still
  unchecked: nested `def`s, and a bound method (`self.f`) used as a value.

### Dogfooding telic on itself

`docs/field-notes.md` has the numbers and the triage. Remaining:

1. Refuted, needing modelling telic lacks: a property's annotated return
   type and immutable frozen-dataclass fields (`ModelCheck.replay`,
   `Prop.__str__`). `typescript._type`/`_expr` are proved with trusted
   predicates (`wf_type`, `wf_expr`, `json_depth`).
2. Counterexamples over unchecked values are rebuilt as JSON
   (`smt.unchecked_json`) for Python and Node only; Rust and Swift still
   show `…` and do not replay them.
3. 70 open: facts about objects and dicts held in fields, callee contracts,
   and termination measures over ASTs (opaque). Few are loop invariants.
4. Put contracts and aims on the pure helpers (`telic/phrase.py`,
   `ears_problems`, `ears_conditions`, `split_by`, `oracle._one`), then add a
   CI job that ratchets `telic.ledger.json` for telic itself.
5. Replaying telic's own counterexamples fails on relative imports inside
   the `telic` package ("could not run").

### Frontends

- **Rust.** Enums with data, tuple structs, `Result` with `?`, traits and
  generics, and `mod x;` across files are modelled (`frontend/rust.py`,
  `frontend/rust_crate.py`). Still unsupported or opaque: enums holding a
  `Vec`, an object or themselves (`Box<Self>`); `ref`/`ref mut` bindings and
  writing through a binding of a `&mut` match; or-patterns that bind names;
  tuples (their items are opaque); for-loops over `zip`/`chunks` with tuple
  patterns; generic arguments that are collections (`Vec<Circle>` for
  `&[T]`); associated types; closures (opaque, captured variables havocked).
  A trait method's contract is assumed for impls telic does not check (of
  unmodelled types, or outside the crate); each such impl is listed as an
  assumption. `str::len` is opaque. There is no Rust fuzzer, though
  `rust_replay.run_rust_samples` runs a function on many inputs in one build
  (the corpus uses it to test proved functions against rustc). A runtime
  check of an `ensures` skips clauses that use `old(...)`.
- **TypeScript.** A subclass of a library class (`extends Component`) and a
  value of an interface type with methods are opaque. Generic type parameters
  are opaque. `instanceof` narrows nothing except `this instanceof` its own
  class.
- **Runtime contracts (`telic run`, the pytest plugin).** Inherited contracts
  are applied only when the base class is in the same module
  (`_with_inherited_contracts` in `telic/runtime.py`).
- **Swift.** `frontend/swift*.py`; what it models and what it does not is in
  [contracts.md](contracts.md) under "Swift". tree-sitter-swift groups mixed
  precedence operators wrongly and attaches prefix operators, `try` and
  postfix chains to the wrong operand; `swift_syntax.py` refolds them, and
  `tests/test_swift.py` compares the result with `swiftc` on random
  expressions. There is no fuzzing for Swift; replay compiles one harness per
  function (cached in the temp directory) and restarts it after a trap.
- **Dart.** Not started. The plan: parse with tree-sitter and follow
  `frontend/rust.py`: sound null safety and 64-bit ints, a corpus, soundness
  exploits, and replay when `dart` is on the PATH.

### Engine (OxCaml, `core/`)

- **No unboxed types, on evidence.** Built with OxCaml `5.2.0+ox` and
  profiled on `telic/` (581 functions; `TELIC_CORE_DEBUG` prints phase
  times). VC generation was 16.5s of a 25s run, and its time went to
  quadratic list membership and repeated heap-key computation, now fixed
  (5.9s). Of what remains, sampling puts about 60% in polymorphic
  comparison and hashing (hash-consing compares sorts structurally) and
  about 14% in the GC; solving is 8.4s. Unboxed layouts can only reduce the
  GC share, so they are not worth their cost yet. The next win is interning
  sorts so hash-cons lookups compare by identity.
- The engine reads the obligation cache through its own keys (`ox:` in the
  cache, a structural digest in `job_key` in `core/main.ml`). Engine-proved
  obligations are also stored under the Python key, but Python-proved ones
  are not visible to the engine.

### Oracles and aims

- **Only Jev has been tested live** (coverage and fact classification). The
  `anthropic` backend has not been run against the real API since it moved to
  the typed-question prompt. Tests cover the prompt and the parsing through
  `llm-cmd`.
- **The builtin coverage judge is lexical.** It matches content words of
  each EARS condition against proved facts. That is fine as a free default,
  but it can call unrelated facts "sufficient" when they share words. Its
  answers are capped at p=0.7, so it never sounds confident.
- **Generative oracles.** `telic gaps --llm` asks a model for realistic
  mutants and stronger contracts (`mutate`, `strengthen`), defaulting to
  `claude -p`. `telic gaps` skips Swift functions: `_lower` in `gaps.py`
  lowers Python, TypeScript and Rust only. The
  builtin `strengthen` only offers the template facts `telic propose` tries,
  so offline it rarely closes a gap. Aim rewrites are shown, never checked.
- **Vacuous-risk is per function.** A safety aim is flagged when every
  function behind it accepts a stub (`return <default>`, `return <argument>`
  or a raise; Python and TypeScript only). A stub
  that returns early from one branch only, or a lemma in a function the
  aim does not list, is not tried.

### Field notes

[field-notes.md](field-notes.md) measured four apps before the oracle and Rust
work. Re-run them when the frontends change.

## Local setup reminders

- The engine builds with `make -C core` from any OCaml >= 5.1 (an OxCaml
  switch, `opam switch 5.2.0+ox`, adds flambda2), Homebrew's included. Without the
  binary, telic uses the Python core (`TELIC_ENGINE=ox` selects the engine).
- Jev: set `JEV_API_KEY` in your environment (never in the repo).
  `telic oracle --probe` checks it.
- Rust replay needs `rustc`, Swift replay `swiftc`; TypeScript needs Node ≥ 18;
  Lean tests skip without Lean.
