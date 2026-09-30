# telic in CI: continuous, cheap, self-maintaining

telic is meant to run on every change, forever, for less than a lint job. Three
mechanisms make that true.

## 1. Evidence is keyed by exact inputs

Every proof is stored as a receipt keyed by what it actually depends on. There
are two levels:

- **Obligations** are keyed by their exact formula, the definitions and lemmas
  it uses, and the verifier identity (a hash of telic's own sources plus the Z3
  version). Reformatting, comments, renames elsewhere, moving a file and
  rebasing all leave the formula unchanged, so the receipt is reused. A telic
  fix or a Z3 upgrade changes the identity, so stale evidence is never trusted.
- **Functions** are keyed by their own source, the source of everything they
  call, the records they use, their Lean sidecar, and the verifier identity. A
  proved function with an unchanged key skips parsing-to-proof work entirely.

Keying by content rather than commit is what makes reuse survive a rebase. In
assay's rebase experiment, 67% of the tasks a real stack touched were still
hash-identical after a clean rebase. A commit-keyed cache re-runs all of them.

## 2. The affected set is exact

`telic ci --since origin/main` checks only what the change can affect. For telic
this is computed, not guessed (`telic/ledger.py`): the affected files are the
changed files, the files importing them (transitively), what the TypeScript
files among them import, the files defining the bases of changed classes (a
call through a base may run an override) and their importers, `@mirrors`
partners, and files sharing an aim with them. No coverage map is involved.

## 3. The ledger ratchets

`telic.ledger.json` is committed. It records every aim (status, linked
functions, the clauses it rests on), every function's status, and every
mirror. `telic ci` compares the change against it:

| change | result |
|---|---|
| aim / function / mirror gets worse | **fails** |
| a clause is dropped from an aim, or an aim is removed | **fails**: weakening a promise is a decision |
| the same, with `Telic-accept: <id> <reason>` in a commit message | passes, and the reason is shown for review |
| something gets better, or is new | passes. `--update` or the pre-push hook records it |

Because the ledger only ratchets, telic can be adopted on a codebase with known
failures: `telic init` snapshots today's state, and from then on nothing may get
worse.

`telic init` writes:

- the ledger;
- `.github/workflows/telic.yml`, where pull requests run `telic ci --since` with
  GitHub annotations, restore the cache from their branch or else from main, and
  never write it. Only pushes to main save it (cache write authority stays with
  the protected branch);
- a pre-push hook that runs the same check locally and keeps the ledger current.
  A regression caught before push costs seconds instead of a CI round trip.

## Measured cost

`python scripts/bench_ci.py` builds a synthetic repository (40 Python + 20
TypeScript modules, 320 functions, 1,780 obligations) and times what CI actually
sees. On a 4-core container:

| situation | seconds |
|---|---|
| cold: empty cache (first run, or a toolchain upgrade) | 12.0 |
| warm: full check, cache restored (push to main) | 0.78 |
| PR touching no checkable file | 0.15 |
| PR editing one function body | 0.45 |
| PR changing one contract | 0.47 |
| PR touching six files | 1.35 |

Raw numbers are in [ci-bench.json](ci-bench.json). The cold number is the only
one that grows with the codebase; the warm and PR numbers grow with the change.
In assay's sample of real commits, 85% of the diffs that touch code change six
files or fewer.

## What is not free

- Refuted and open functions are re-examined on every run, because their
  diagnostics (replayed counterexamples, fuzzing) are the point. They're also
  the failing part of the build.
- Lean escalations cost seconds each, but only on the first run: proved results
  are receipts too, and sidecar proofs are re-checked only when their text or
  statement changes.
- `telic gaps` (mutation) is deliberately not part of `telic ci`. Run it when
  writing or changing a contract, not on every push.
