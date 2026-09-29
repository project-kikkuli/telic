# Handoff: known gaps

This lists what telic does not do yet, or does only partly, as of `16f1cf5`. Each item says where it lives and what
done looks like. Soundness items come first: they can make telic say
`proved` when it shouldn't.

## Soundness

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
  `@trusted` callee's `@ensures` that is unsatisfiable mid-body; an entry
  check Z3 cannot decide leaves the verdict alone.

## Dogfooding (task 15)

`docs/field-notes.md` has the numbers and the triage. Remaining:

1. The four refuted functions whose preconditions telic cannot state
   (`vcgen.pack`, `typescript._type`/`_expr`, `html._line_status`): they need
   specs over `components()`, a JSON schema, and quantifiers over dict keys.
2. 92 open, mostly loops without invariants and termination of recursion
   over ASTs (opaque, so no measure).
3. Put contracts and aims on the pure helpers (`telic/phrase.py`,
   `ears_problems`, `ears_conditions`, `split_by`, `oracle._one`), then add a
   CI job that ratchets `telic.ledger.json` for telic itself.
4. Replaying telic's own counterexamples fails on relative imports inside
   the `telic` package ("could not run").

## Frontends

- **Rust.** Unsupported: data-carrying enums (`enum Shape { Circle(u32) }`),
  tuple structs (`p.0`), traits and generics (`T: Clone` values are opaque), and
  modules in other files (`mod x;`; inline `mod x { }` works). `str::len` is
  opaque. There is no fuzzing for Rust, and a runtime check of an `ensures`
  skips clauses that use `old(...)` or `implies(...)`
  (`frontend/rust_replay.py`).
- **TypeScript.** `class B extends A` is recorded as a note, not modelled:
  inherited fields and methods are opaque (Python inheritance is fully
  modelled).
- **Runtime contracts (`telic run`, the pytest plugin).** Inherited contracts
  are applied only when the base class is in the same module
  (`_with_inherited_contracts` in `telic/runtime.py`).
- **Swift and Dart (task 17).** Not started. The plan: parse with tree-sitter
  (check PyPI wheels for tree-sitter-swift and tree-sitter-dart) and follow
  `frontend/rust.py`. Swift: overflow traps, optionals and value structs. Dart:
  sound null safety and 64-bit ints. Each gets a corpus, soundness exploits,
  and replay when `swiftc` or `dart` is on the PATH.

## Engine (OxCaml, `core/`)

- **No unboxed types.** The sources use no unboxed layouts, so the Makefile
  no longer passes `-unboxed-types`; any OCaml >= 5.1 builds the engine
  (`OCAMLFLAGS` passes local flags). What makes it fast is native code,
  hash-consing and one Z3 per domain. *Done:* hot records such as terms and
  obligations use unboxed layouts, and `TELIC_CORE_DEBUG` timings show the
  difference.
- The engine reads the obligation cache through its own keys (`ox:` in the
  cache, a structural digest in `job_key` in `core/main.ml`). Engine-proved
  obligations are also stored under the Python key, but Python-proved ones
  are not visible to the engine.

## Oracles and aims

- **Only Jev has been tested live** (coverage and fact classification). The
  `anthropic` backend has not been run against the real API since it moved to
  the typed-question prompt. Tests cover the prompt and the parsing through
  `llm-cmd`.
- **The builtin coverage judge is lexical.** It matches content words of
  each EARS condition against proved facts. That is fine as a free default,
  but it can call unrelated facts "sufficient" when they share words. Its
  answers are capped at p=0.7, so it never sounds confident.
- **Aim redesign (task 11) is still open.** Remaining: `telic aims
  --json` should carry the per-part judge answers, and the HTML report should
  show judgments with the oracle and probability, as the terminal does.

## Docs

`docs/field-notes.md` reports four apps measured before the oracle and Rust
work. Re-run them to refresh the numbers when the frontends change.

## Local setup reminders

- The engine builds with `make -C core` from any OCaml >= 5.1 (an OxCaml
  switch, `opam switch 5.2.0+ox`, adds flambda2). Homebrew's OCaml on a
  newer macOS than its SDK needs
  `OCAMLFLAGS="-ccopt -Wl,-U,_dup3 -ccopt -Wl,-U,_pipe2"`. Without the
  binary, telic uses the Python core (`TELIC_ENGINE=ox` selects the engine).
- Jev: set `JEV_API_KEY` in your environment (never in the repo).
  `telic oracle --probe` checks it.
- Rust replay needs `rustc`; TypeScript needs Node ≥ 18; Lean tests skip
  without Lean.
