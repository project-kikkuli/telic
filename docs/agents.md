# telic with a coding agent

An agent that writes code fast needs a critic that is precise, fast, and
impossible to argue with. `telic check --json` is that critic: every finding is
anchored to a line, and each one comes with an executed counterexample, a missing
invariant, or a Lean goal.

## The loop

0. **On existing code, start with `telic propose --json`.** It returns facts
   telic has proved about the code as it is, and preconditions that would make
   crashing functions crash-free. Adopt a fact only if it is what the code
   *should* do; a fact that looks wrong is a bug report. `--intents` adds
   drafted requirements (the user decides which are real).
1. **State the intent** where the code lives, one EARS sentence per
   requirement, listing the functions that back it:
   `#@ intent SPLIT-EXACT: WHEN a bill is split, the app shall assign every cent to exactly one person.`
   `#@   by: split_bill`
2. **Write the lemmas** with the functions: `@requires` for what callers must
   guarantee, `@ensures` tagged with the intent (`#@ [SPLIT-EXACT] ensures ...`)
   for what each function promises towards it.
3. **Run `telic check --json`** and handle each non-`proved` obligation:
   - `refuted` with `replay.confirmed: true`: the code violates the contract on
     real inputs. Fix the code, or fix the contract if the contract is wrong.
     Never both at once without saying so.
   - `unconfirmed`: the solver's counterexample is unreachable. Add or strengthen
     a loop `@invariant` (the report names the loop).
   - `unknown`: run `telic prove --agent …`, or write the Lean proof yourself from
     `telic lean <id>`.
   - `problems` / `unsupported`: rewrite into the supported subset (the message
     says what's wrong), or isolate the construct behind a `@trusted` function
     and say why.
4. **Run `telic gaps`** on what you proved. Each surviving mutant is a wrong
   implementation your contract accepts. Strengthen `@ensures` until none survive,
   or until you decide the remaining freedom is intended.
5. **Check the intents with `telic intents`.** Each should be `backed` (every
   lemma proved) with its links intact. Whether the lemmas cover the sentence is
   the user's review (`--accept`), or at most a model's labelled judgment
   (`--judge`); never claim an intent is proved.
6. **Commit when `telic check --strict` passes.**

## Rules worth giving an agent

- Never weaken an `@ensures` to make a proof go through without saying so in the
  commit message.
- Prefer `@requires` over defensive code for conditions the caller controls;
  prefer `@raises` for conditions the caller can't control.
- Don't add `@assume` or `@trusted` to silence telic. Both show up in every
  report as trusted base.
- Keep functions small and loop-free where possible: loop-free functions become
  logical definitions usable in other contracts, and they are proved without
  invariants.

## Claude Code skill

Copy [`skills/telic/SKILL.md`](../skills/telic/SKILL.md) into your project's
`.claude/skills/telic/` directory to teach Claude Code the loop above.

## Proving in Lean with an agent

```bash
telic prove --agent "claude -p"            # any command that reads a prompt on stdin
telic prove --agent "claude -p" --id 'f/ensures@12>18' --attempts 6
```

The agent receives the source function, the obligation, and the complete Lean
file (definitions, unfolding lemmas, and the theorem with `sorry`). It must reply
with a tactic proof. Lean's errors go back to it, up to `--attempts` times.
Accepted proofs are written to `<file>.proof.lean`. Commit that file: the proofs
are the evidence.
