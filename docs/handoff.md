# Handoff: known gaps

This lists what telic does not do yet, or does only partly, as of the oracle
commit (`1c40d4d`) plus this docs pass. Each item says where it lives and what
done looks like. Soundness items come first: they can make telic say
`proved` when it shouldn't.

## Soundness

- **Duplicate class names across files.** When two checked files define a
  class with the same name, every function that mentions that name is reported
  unsupported (`Program.ambiguity` in `telic/program.py`). This is sound but
  blunt: telic's own `FunctionLowerer` (in both `frontend/python.py` and
  `frontend/rust.py`) is unchecked because of it. *Done:* classes are keyed by
  module (e.g. `rust.FunctionLowerer`) in the IR, the heap keys and the engine,
  and imports resolve to the right one.
- **`telic ci` misses overrides in other files.** A call through a base class
  depends on every override (`Program.dispatch`). `affected_files` in
  `telic/ledger.py` adds the files that import a changed file, but not the files
  that call a method a changed file overrides. If a subclass in `c.py` changes
  an override's contract, a caller in `a.py` that only imports the base from
  `b.py` is not re-checked by `telic ci --since`. A full `telic check` is
  correct. *Done:* the affected set includes callers of overridden methods,
  with a test.

## Dogfooding (task 15)

`telic check telic/` now runs to completion: 105 proved, 59 refuted, 12 open,
5 problems, 312 unsupported, 223 with nothing to check. Nobody has triaged the
results yet. The 59 refutations are mostly crash obligations (index, key,
None) in functions without contracts, so some will be real bugs and some will
be modelling gaps. *Next:*

1. Triage the refutations: fix real bugs, and turn modelling gaps into
   frontend fixes with a corpus case.
2. Reduce the unsupported count: list the top reasons
   (`telic check telic/ --json`) and fix the most common idioms.
3. Put contracts and aims on the pure helpers (`telic/phrase.py`,
   `ears_problems`, `ears_conditions`, `split_by`, `oracle._one`), then add a
   CI job that ratchets `telic.ledger.json` for telic itself.

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

- **No unboxed types yet.** The Makefile passes `-unboxed-types`, but the
  sources use no unboxed layouts, and if the flag is rejected the build
  silently falls back without it. What makes the engine fast today is native
  code, hash-consing and one Z3 per domain. *Done:* hot records such as terms
  and obligations use unboxed layouts, the fallback is not silent, and
  `TELIC_CORE_DEBUG` timings show the difference.
- **The engine does not read the obligation cache.** It writes receipts for
  proved obligations, but it re-solves every obligation of a function it
  handles. Function-level receipts are still reused. *Done:* obligation keys
  are sent to the engine and cached obligations are skipped.

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

- The OxCaml engine needs an OxCaml switch (`opam switch 5.2.0+ox`) and
  `make -C core`. Without it, telic uses the Python core
  (`TELIC_ENGINE=ox` selects the engine).
- Jev: set `JEV_API_KEY` in your environment (never in the repo).
  `telic oracle --probe` checks it.
- Rust replay needs `rustc`; TypeScript needs Node ≥ 18; Lean tests skip
  without Lean.
