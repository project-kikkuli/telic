---
name: telic
description: Verify Python/TypeScript functions against intents and contracts written as #@ / //@ comments. Use when writing or changing business logic, when a function has #@/ //@ contracts, or before committing code that carries intents.
---

# telic: prove it, don't vibe it

This project states intent and contracts in comments and verifies them with
`telic`. Follow this loop for any function you write or change:

1. If the change serves a requirement, declare or link it. Declare it anywhere,
   as one EARS sentence, and list the functions that back it:
   `#@ intent ID: WHEN <trigger>, the <system> shall <response>.` followed by
   `#@   by: fn_a, Class.method, web/x.ts::fnB`. Then write `#@ intent ID` in
   each of those functions. `telic intents` checks both directions.
2. Write `#@ requires` (what callers must guarantee) and `#@ ensures` (what the
   function promises; `result` is the return value, `old(e)` is an entry value).
   Use `//@` in TypeScript.
3. Run `telic check --json <files>` and resolve every non-`proved` obligation:
   - `refuted` with `replay.confirmed`: a real bug on real inputs. Fix the code
     (or the contract, if the contract is wrong, and say which).
   - `unconfirmed`: add or strengthen a loop `#@ invariant`.
   - `unknown`: `telic prove --agent "claude -p"` or write the Lean proof from
     `telic lean <id>`.
   - `unsupported`/`problems`: rewrite into the supported subset as the message says.
   - trusted base growing: annotate types (opaque values prove nothing about
     themselves) and put contracts on the functions you call.
4. Run `telic gaps <files>` and strengthen `#@ ensures` until no mutant survives
   (or the surviving freedom is intentional, and you say so).
5. Never add `#@ assume` or `#@ trusted`, and never weaken a contract, just to
   make telic pass.

Reference: docs/contracts.md in the telic repository.
