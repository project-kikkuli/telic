# Field notes: telic on real apps

telic was run, unmodified and with no contracts added, on four open-source
apps shaped like typical generated code: CRUD backends and a React front end.

| app | stack | before | after | time |
|---|---|---|---|---|
| fastapi-realworld-example-app | FastAPI, pydantic, asyncpg | frontend crash; then 14 false refutations, 37 problems, 28 unsupported | 8 proved, 96 with nothing to check | 0.5s |
| full-stack-fastapi-template (backend) | FastAPI, SQLModel | 2 false refutations, 1 unsupported | 7 proved, 52 with nothing to check | 0.2s |
| node-express-realworld-example-app | Express, Prisma | 7 unsupported, 1 problem, 1 spurious error | 7 proved, 24 with nothing to check | 0.3s |
| chatbot-ui (lib/, components/utility) | Next.js, React | 17 unsupported, 9 problems | 11 proved, 36 with nothing to check, **1 real crash** | 0.8s |

"Before" is telic as it was when these runs started; "after" was re-measured
at `16f1cf5` (Python 3.14, `--no-lean --no-cache`, upstream `main` of each
app on 2026-09-29). Each gap found was fixed in the frontends or engines,
with a regression case or soundness exploit added to the test suite. The
full-stack template's file in Python 3.14 syntax now parses, which is where
its three extra functions come from.

## What it found

`adaptMessagesForGeminiVision([])` in chatbot-ui reads `messages[0].parts`
without checking for an empty list. telic reports it and replays it in Node.

## What the gaps were

Mostly idioms, not deep semantics:

- class inheritance, pydantic models, and library base classes;
- `x or default`, `str + str`, `xs + ys`, `f(**kw)`, JSON-like dict literals;
- empty `[]`/`{}` typed by their first use;
- generators;
- JSX, destructured props, `push(...xs)`, `map` with any callback;
- `let x;`.

A few were soundness bugs, now fixed:

- an overridden method used as a logical definition;
- `await` assuming invariants across shared field maps;
- an uninterpreted function used at two signatures, which made z3 reject
  the query.

## telic on itself

`telic check telic/` (`--no-lean --no-cache`, 38 files, 734 functions):

| | refuted | open | proved | nothing to check | unsupported | problems |
|---|---|---|---|---|---|---|
| `9bf7e76` | 17 | 51 | 106 | 230 | 314 | 5 |
| `16f1cf5` | 6 | 92 | 144 | 254 | 239 | 4 |
| `e4c60a2` (48 files: `telic/ui/` added) | 11 | 102 | 162 | 306 | 278 | 6 |
| `45d034a` | 7 | 70 | 182 | 323 | 279 | 6 |
| `4ef8dc7` (every recursion needs a termination proof again) | 7 | 107 | 163 | 313 | 282 | 6 |

The 17 refuted functions were triaged:

- **A real bug.** `lean._first_error` raised `IndexError` when the first
  error was blank.
- **A soundness bug in telic.** A method's `@ensures` lemma held for every
  heap, not only for objects satisfying the class invariant, so the theory
  could prove a false contract (`tests/cases/soundness/t27.py`).
- **Missing preconditions**, now stated with `@requires` or a class
  invariant: `restore_receipt`, `Program.ref`, `VCGen.alloc_facts`,
  `VCGen.apply_def`, `_lower_safely`, `_block_end`, `value_boolop` and
  `propose.Syntax`. `VCGen.heap_keys` now reports an unknown class as a
  `VCError` instead of a `KeyError`.
- **Verifier false positives**, fixed in the verifier: a termination
  counterexample reported as a refutation (no finite run witnesses one),
  and a field telic cannot model failing every function in the program
  instead of only the ones touching it.

Six remain refuted: the demo's planted bug (`refund_amount` and its
`@mirrors` pair), and four whose preconditions telic cannot state yet:
`vcgen.pack` (arity depends on the type), `typescript._type` and `_expr`
(well-formed JSON from `lower.mjs`), and `html._line_status` (needs a loop
invariant quantifying over a dict's keys).

Second pass (`e4c60a2` to `45d034a`):

- `vcgen.pack` and `html._line_status` now state and prove their
  preconditions, with two contract-language additions: quantifiers over a
  dict's keys (`all(p(k) for k in d)`) and `isinstance(x, (A, B))` as one
  predicate per class.
- A real bug: `viewports = []` in `telic.toml` crashed `run_app`.
- Open fell by 32, almost all from requiring termination only where a
  recursion group makes a claim or is a logical definition (as for loops).
  Loop invariants are not what the rest need: of the 50 open functions (not
  counting errors) at that point, 5 have a loop state a stronger invariant
  would rule out, and Houdini inference already closes 1 of them. The rest
  need facts about objects and dicts held in fields (27), callee
  contracts (8) and termination measures over ASTs (3).
- Still refuted: the demo's planted bug, `typescript._type`/`_expr` (their
  precondition is "well-formed JSON from `lower.mjs`", a recursive schema
  over `Any` values telic cannot state), `ModelCheck.replay` and
  `Prop.__str__` (need a property's annotated return type, and frozen
  dataclass fields that calls cannot change), and `run_app` (every viewport
  must report on every lemma).

Unsupported fell by 75: 37 functions from telling telic's same-named
classes apart (`FunctionLowerer`, `ExprLowerer` in the Python and Rust
frontends), and 39 from `for a, b in pairs` loops. Open rose because functions that became checkable, and
callers of the new preconditions, have obligations Z3 cannot close without
loop invariants.

## TypeScript classes and idioms

TypeScript was brought to parity with Python's classes (`extends`, overrides
and dispatch, `super`, abstract classes, inherited invariants) and learned
discriminated unions, interfaces that extend interfaces, and unawaited async
calls. Two TypeScript sources were then checked, `--no-lean --no-cache`,
before (`f8e8802`) and after:

| source | before | after |
|---|---|---|
| examples/ui/notes-react `src/` (React, 20 files) | 1 proved, 24 with nothing to check, 1 unsupported | 1 proved, 25 with nothing to check |
| vultix/ts-results `src/` (`910789d`) | 50 with nothing to check, 4 unsupported | 54 with nothing to check |

The blockers were idioms:

- `[...notes].sort(...)`: sorting a fresh array was rejected like sorting a
  shared one;
- `import { None } from "./option"`, where `None` is both a `const` and a
  `type`: the import kept only the type;
- `if (!(this instanceof ErrImpl)) return new ErrImpl(v)` in a constructor, a
  guard for calls without `new`, which a class constructor never gets.

Neither source makes claims, so nothing new is proved. The soundness review
behind the class work found four holes, now closed, each with an exploit in
`tests/cases/soundness/`:

- a subclass invariant over an inherited field, broken by code typed as the
  base and then assumed by an override (Python too, `inh1.py`);
- a base constructor calling a method the subclass overrides before the
  subclass set its fields (`inh2.py`, `inh2.ts`);
- a call to an async function without `await`, whose postcondition was
  assumed as if it had finished (Python too, `async1.py`);
- `void f()`, which dropped the call.

## Swift

The Swift frontend was run on [mxcl/Version](https://github.com/mxcl/Version)
`Sources/` at `3043fcd` (5 files, 376 lines, 13 functions), unmodified and
with no contracts added, `--no-lean --no-cache`:

| | refuted | proved | nothing to check | unsupported |
|---|---|---|---|---|
| first run | 1 | 1 | 3 | 8 |
| after the fixes below | 1 | 2 | 5 | 5 |

**A real crash.** `Version(Int.min, 0, 0)` traps: the initializer takes
`abs` of each component, and `abs(Int.min)` overflows. telic reports it for
each of the three components and replays each one: `swiftc` compiles the
package's own `Version.swift` with a generated harness and the call traps.

The run found these gaps, now fixed:

- `self.init(...)` delegating to another initializer, and `self = v` in a
  struct initializer;
- `"-" + ids.joined(separator: ".")`, which tree-sitter-swift parses as a
  call of `"-" + ids.joined`;
- `String` methods whose result type telic does not know (`firstIndex(of:)`),
  which were typed as `String`.

Still unsupported: `#if` inside a function body, a local function,
`1...3 ~= n`, `for (a, b) in zip(...)`, and `Version.init(tolerant:)` used
as a function value.

The Swift corpus, compared engine against Python core, also found a bug in
the native engine: its JSON reader turned integers too wide for an OCaml
`int` into floats, so `Int.max` became 2^63 and it proved that
`-Int.min` and `Int.min / -1` do not overflow. Both engines now read those
integers exactly.

## What it means

Most functions in glue code have **nothing to check**. They have no contract
and no operation that can fail, and telic now says so instead of calling
them "proved". The trusted base lists what the rest relies on: every
library call, and that values from libraries have their annotated types.

Silence is the right default for code that makes no claims:

- an intentional `raise HTTPException` is not a bug;
- neither is a `while (true)` stream reader.

telic becomes useful once aims and contracts state what the app must do.
The proofs are only as strong as the claims they prove.
