# Contract reference

A contract line is a line comment starting with `#@` (Python) or `//@`
(TypeScript, Rust), followed by a keyword. The payload is an expression in the host
language. A line whose first word is not a keyword continues the previous clause:

```python
#@ ensures all(result[i] <= result[i + 1]
#@             for i in range(len(result) - 1))
```

An unknown keyword, or a contract line not attached to anything, is an error.
telic never ignores a contract silently.

## Where contract lines go

| keyword | attaches to | placement |
|---|---|---|
| `requires`, `ensures`, `decreases`, `raises`, `aim`, `mirrors`, `trusted` | a function | contiguous comment lines directly above the `def`/`function`, or the first lines of its body |
| `invariant`, `decreases`, `index` | a loop | directly above the loop header, or the first lines of its body |
| `assert`, `assume` | a statement position | anywhere inside a block |
| `aim ID: sentence` | the module | anywhere outside a function |
| sentence | a directory | an `aims/<ID>.md` file (see [Cross-file aims](#cross-file-aims)) |
| `[ID] ui NAME: property` | the running app | a comment in any file of the app (see [UI lemmas](#ui-lemmas)) |

## Clauses

**`requires P`** is a precondition. Callers must establish it; the body may
assume it. Preconditions are evaluated in order, and each may rely on the earlier
ones.

**`ensures Q`** is a postcondition, checked at every `return`. In `Q`:
- `result` is the return value;
- a scalar parameter means its value **at entry** (reassigning it in the body
  doesn't change what callers passed);
- a list parameter means its contents **at exit**, which is what the caller sees;
- `old(e)` evaluates `e` at entry.

**`invariant I`** is a loop invariant. It must hold before the loop and be
preserved by every iteration, including iterations that `continue`. After the
loop it is assumed, together with the negated condition. For `for i in
range(lo, hi)` and `for (let i = lo; i < hi; i++)`, invariants see `i` as the
index of the *next* iteration, so `i == hi` after the last one (Dafny's
convention). For `for x in xs` / `for (const x of xs)`, name the counter with
`@index k` or use `enumerate`.

**`decreases E`** is a termination measure: an integer that is non-negative and
strictly decreases on every loop iteration or recursive call. It is optional:
telic tries measures derived from the loop condition (`hi - lo + 1`, `len(xs) - i`,
…) or from the parameters, and proves whichever works. When nothing works,
termination is reported as open.

**`raises C`** is for exceptions you intend. A `raise`/`throw` must only be
reachable when `C` holds, and the function must not return normally when `C`
holds. In a function with a contract, a reachable `raise` without `@raises` is
an error; without any contract, raising is simply what the function does (a
handler rejecting a request). A Rust `panic!` is always a crash to rule out.

**`assert P`** is proved statically, then assumed. Native `assert` statements are
treated the same way, except an `assert` about values from unchecked code (a
library result, an untyped input): that is a runtime check of the
environment, so it is treated like a `raise`.

**`assume P`** is assumed without proof. It's an escape hatch and is listed in
every report under *trusted base*.

**`trusted`**: the function's contract is assumed and its body not verified
(FFI, performance hacks). Also listed under *trusted base*.

## Aims

An aim is a top-level requirement, written for a reviewer as one EARS
sentence. It is not a formula, and telic never reports one as "proved".

```python
#@ aim REFUND-CAP: WHEN a refund is requested, the shop shall refund at most
#@   what the customer paid, net of earlier refunds.
#@   by: refund_amount, Ledger.apply, web/checkout.ts::refundButton
```

Declare an aim anywhere in the project; IDs are `UPPER-KEBAB` and unique
project-wide. What telic proves are **lemmas** one layer below: contract clauses
that cite the aim. `#@ aim ID` inside a function tags every following
clause, and `#@ [ID] ensures …` tags one clause. An aim's lemmas can be spread
over many functions, files and both languages, and an `@mirrors` equivalence
counts as a lemma too.

**Two-sided links.** `by:` points down from the aim to the functions that
back it, and citations point back up. telic checks both directions: a `by:` entry
that does not cite the aim, or a function that cites it without being listed,
is reported, and `telic aims` fails on it. `by:` accepts `name`,
`Class.method` or `path::name`.

### Cross-file aims

Cross-file aims live in `aims/<ID>.md`, one file per aim, in the
lowest directory that contains all the code the aim constrains. Its scope is
the directory holding `aims/` and everything below it; `aims/` at the
root is repo-scoped. An aim that concerns one file stays a comment in that
file.

```markdown
<!-- aims/PRICE-AGREE.md -->
WHEN a customer checks out, the checkout page shall show exactly the amount the
server charges.
by: discounted_total, web/checkout.ts::displayTotal
```

The filename is the ID, under the same rules as a comment ID; a file named
otherwise is reported. Besides aim files, `aims/` may hold only a README and
hidden files; any other file or subdirectory is reported. An `aims/` reached
through two symlinks is read once, at the wider scope. The contents are one EARS sentence, then an optional
`by:` line, with no heading. Code cites the aim exactly as it cites a
comment-declared one.

- **One ID space.** Comments and aim files share IDs. Declaring a sentence
  for the same ID twice, in either place, is reported.
- **Scope.** Every lemma and `by:` target of a file-declared aim must live
  under its scope, judged by real path through symlinks.
- **Orphans.** A file-declared aim nothing backs makes `telic aims` and
  `telic ci` fail.
- **Sprawl.** A file-declared aim whose lemmas all sit in one code file gets
  a note to declare it there as a comment instead.
- **Partial checks.** Checking a file or directory also reads every `aims/`
  directory above it, and reports their aims where the checked code cites
  them.

`telic aims --for PATH` lists what governs a file or directory: aims
declared in `aims/` directories above or inside it, declared or cited in its
code, or naming its functions in `by:`. It only parses; nothing is proved.

**EARS.** The sentence is linted against the EARS patterns:
`The <system> shall …`, `WHEN <trigger>, the <system> shall …`, `WHILE …`,
`IF … THEN …`, `WHERE …`, and combinations of them. One `shall`, one sentence.

**Status** says what the lemmas establish:

`backed` (every lemma proved) · `broken` (a lemma refuted) · `partial` (some
open) · `vacuous-risk` (see below) · `unbacked` (declared, nothing cites it) ·
`undeclared` (cited, never declared).

**Safety needs liveness.** An aim that forbids something ("shall never",
"shall not", "must not") is easy to back with lemmas an empty function also
meets: `ensures result >= 0` holds of `return 0`. For each such aim that is
otherwise backed, telic checks stubs of every function its lemmas sit on (an
immediate `return` of a default value, and an immediate `raise`) against
that function's whole contract. If a stub passes for every one of them, the
aim is `vacuous-risk` and the stub is named. Add a lemma that says what the
function still does (`ensures result == a + b`, or a `@raises` that pins
down when it fails); a mirror or ui lemma counts too. A `vacuous-risk` aim
can't be `--accept`ed.

**Coverage** is a separate question: do the lemmas cover the requirement? A
prover can't answer it, so telic records an answer instead:

```
telic aims --accept REFUND-CAP      # you reviewed it: pinned to a digest of
                                       # the sentence and the lemma set
telic aims --judge                  # an oracle's opinion, cached by the same
                                       # digest, labelled "judged" with who and p
```

A judgment also answers each part of the EARS response on its own.
`telic aims --json` carries them under `coverage.parts` (condition, `p`, and
the oracle that answered), and `telic report` lists them under the aim with
the oracle and probability.

**How the layers line up.** An aim says *what* the system must do, in
words. A contract clause says one precise, checkable thing about one function.
Each clause that cites an aim is one lemma for it, and an aim usually
needs several, in different functions and files, each checked on its own. The
clause is proved; the aim is only ever "backed", because nothing proves that
the lemmas add up to the sentence. That is what the review records.

**Proposals.** `telic propose PATHS` works bottom-up from existing code:

- *facts*: candidate postconditions (bounds, relations to parameters, lengths,
  what a method leaves unchanged), each kept only if telic proves it about the
  code as it is. It describes behaviour, not intent, so a fact can be a bug
  written down.
- *crash-free preconditions*: for each function that can crash, the weakest
  simple `requires` that removes every crash (callers then owe it).
- *draft aims* (`--aims`): each proved fact written as an EARS
  sentence ("WHEN saturating returns, the result shall be at most a"), then
  sorted by an oracle into requirements, implementation details and likely
  bugs (shown as *suspicious*). A generative oracle may rephrase a draft
  (kept only if it passes the EARS lint) and name requirements nothing proves
  yet (shown as unbacked). Drafts are never written to your code.

`--write` inserts the facts (and, with `--with-fixes`, the first precondition);
`--json` is for agents.

A review goes stale when either the sentence or the lemma set changes.

## Oracles

Some steps need judgment no proof gives: whether an aim's lemmas cover it,
which proved facts read as requirements, and, in `telic gaps`, what a
realistic bug looks like and what a stronger contract would say. All go
through one protocol: typed questions about a state, the shape of a System
One classifier.

```json
{"task": "coverage",
 "state": {"requirement": "WHEN ..., the shop shall ...", "facts": [...]},
 "questions": {"covers": {"type": "noul", "instructions": "...",
                          "criteria": {"true": "...", "false": "..."}}}}
```

The answer is `{"answers": {"covers": {"noul": 0.91}}}`. Question types are
`noul` (yes/no, a probability), `choice` (one of the criteria's keys, with
probabilities), `score` (a rating over levels) and `text` (free text, which
only generative backends answer). A backend may leave any question out, and
the next one in the chain gets it. Coverage asks one `noul` per part of the
EARS response, so an insufficient verdict names the missing part without
generating text. Probability ≥ 0.6 is "sufficient", ≤ 0.4 "insufficient",
and anything between is "uncertain".

| `--oracle` / `TELIC_ORACLE` | |
|---|---|
| `builtin` | deterministic rules: word overlap for coverage, clause shape for facts; local and free |
| `jev[:MODEL]` | TypeSafe's Jev System One classifier; `JEV_API_KEY` (or `TYPESAFE_API_KEY`) |
| `http:URL` | POSTs the request above; `TELIC_ORACLE_TOKEN` is sent as a bearer token |
| `cmd:COMMAND` | the request on stdin, the answers on stdout |
| `py:MODULE:FUNC` | `FUNC(task, state, questions)` returns the answers |
| `anthropic[:MODEL]` | an LLM prompted for the typed answers; `ANTHROPIC_API_KEY` |
| `llm-cmd:COMMAND` | the same prompt on stdin, the model's reply on stdout |
| `NAME[:ARG]` | a plugin under the `telic.oracles` entry point group |

Chain backends with `then` (`jev then anthropic`); the builtin always ends
the chain. `TELIC_ORACLE_COVERAGE`, `TELIC_ORACLE_CLASSIFY_FACTS`,
`TELIC_ORACLE_MUTATE` and `TELIC_ORACLE_STRENGTHEN` override one task. With
nothing set, telic uses `TELIC_JUDGE_CMD`, then Jev, then Anthropic,
whichever credentials are present, and the builtin otherwise; with Jev set
and the `claude` CLI on the PATH, `claude -p` follows Jev for what it
leaves unanswered. The two generative tasks, `mutate` and `strengthen`,
which Jev can't answer, use `llm-cmd:claude -p` by default.
Answers are cached under `.telic/`, so CI asks once per change. `telic oracle
--probe` shows what answers each task and sends one sample question.

## Gaps

`telic gaps PATHS` attacks the contracts of proved functions. Each mutant is
checked against the unchanged contract; one that still proves, and that a
witness input shows behaves differently, is a gap.

- *Operators*, always, and deterministic: flip a comparison, shift a
  constant, delete an update, return something else, negate a condition;
  and one realistic bug per category, made by deleting the first matching
  guard or unwrapping the first `try`: a missing None check, a skipped
  validation, a skipped authorization check, removed error handling, a
  deleted guard clause.
- *Model mutants*, only with `--llm` (task `mutate`, `claude -p` by
  default): the model sees the function, its contract and the aims it cites,
  and writes the whole function with one bug per category. A mutant that
  edits the contract, renames the function or falls outside the supported
  subset is counted as unusable, never as killed.
- *Proposals* (task `strengthen`): for the gaps that survive, telic proposes
  `@ensures` clauses: the template facts `telic propose` tries, or with
  `--llm` the model's clauses and, if the function cites an aim, a rewritten
  aim. A clause is shown only if the original still proves with it and it
  rejects at least one surviving mutant; the output says how many. An aim
  rewrite is a sentence and is shown as unchecked. Nothing is written to
  your code.

`--oracle SPEC` picks the model (and implies `--llm`); `--no-propose` skips
proposals. Answers are cached under `.telic/`.

## Mirrors

```ts
//@ mirrors ../server/pricing.py::quote
```

The path is relative to the declaring file; the named file is loaded
automatically. The two functions must take the same number of parameters (matched
by position) and must agree on every input both preconditions accept. An `int`
parameter against a `number` parameter is compared on integers.

## UI lemmas

A UI lemma is a property of the running app, checked through its
accessibility tree (roles, names, states), whatever the framework. It is a
contract line with the `ui` keyword, written in a comment in any file of the
app (`//@`, `#@`, `--@` or `<!--@ ... -->`, so `.svelte`, `.jsx` and `.html`
files work too), and it cites its aims with a tag:

```ts
//@ aim ESCAPE: WHILE a dialog or menu is open, the app shall let the user
//@   return to the home screen.
//@   by: escape
//@ [ESCAPE] ui escape: always reachable home from overlay
```

`by:` names ui lemmas like functions; both directions are checked. An
`@aim ID: sentence` in a file no language frontend reads (a `.svelte` or
`.jsx` file) is picked up too.

| property | holds when |
|---|---|
| `always reachable P [from Q]` | from every reachable state (where `Q` holds), some sequence of actions reaches `P` |
| `reachable P` | some reachable state satisfies `P` |
| `always P [while Q]` / `never P [while Q]` | every reachable state (where `Q` holds) satisfies `P` / not `P` |
| `unobscured T [while Q]` | wherever `T` renders, its center and four corners hit `T` (or its label) at every viewport |
| `persists T` | changing control `T` and reopening the app (stored data kept) shows the new value |

Any property can end with `via FUNC`: the function that handles the change.
Its own verdict then counts toward the lemma (a refuted handler refutes it).

Predicates: `home` (the first screen, nothing open), `overlay` or `overlay
"Name"` (a dialog, alert dialog or menu is open), `screen "/notes/*"` (glob),
`ROLE "name"` (present), `ROLE "name" is enabled|disabled|checked|unchecked|
expanded|collapsed|selected|pressed`, `ROLE "name" == "value"`, joined with
`not`, `and`, `or` and parentheses. A name is exact (`"Close"`) or a regex
(`/close|done/i`); a role alone matches any name.

**How it is checked.** telic starts the app, and learns its state graph from
it: from a fresh start (new browser profile) it fires every action a user
has (click, type, choose, `Escape`) in every state it finds, and abstracts
each screen to the route, the open overlays, the controls and their states,
and the lemmas' predicates. Returning to a state replays its path from a
fresh start. Then random walks through the model are replayed in the app;
a step the model did not predict is added to it and learning resumes. The
model is judged by the app, never the other way round.

What counts as a different state is chosen so data does not make the model
infinite: items of a list are acted on through the first item only and the
list's length counts as 1 or more; numbers in names are blanked; which box is
checked or which option chosen is data unless a lemma names it; a form's text
fields are filled in and sent as one action; live regions (toasts, status
messages) are not part of a state. If telling controls apart still gives more
than 100 states, a state is just the screen, the open overlays and menus, the
landmarks and the lemmas' predicates (`abstraction = "screens"`), and each
route the model promises is replayed with re-planning from wherever the app
actually is.

An element behind a modal dialog it is not part of cannot be operated, so it
is neither covered nor counted for `unobscured`; an action on a covered
element is blocked, as it would be for a person.

**Statuses** say what they rest on:

| status | means |
|---|---|
| proved on the learned model | holds in every state of a *complete* model (every action fired in every state); routes the model promises are replayed in the app |
| proved by a replayed witness | `reachable`: the path was replayed in the app |
| unobscured wherever it renders | hit-tested in every state where it renders, at every viewport ("uncovered in 23/23 states") |
| passed the test | `persists`: changed, reopened, still changed |
| refuted | with the action trace, replayed in the app before it is reported |
| open | exploration stopped at a budget, or a trace did not replay |
| vacuous | no reachable state made it relevant: never counted as passed |

Each model is shown with its size, whether exploration finished, how
conformance testing went, and how many transitions were nondeterministic
(hidden state the abstraction does not see). The whole model is written to
`.telic/ui-model-<viewport>.json` next to the app.

**The app.** The nearest `telic.toml` with a `[ui]` section above the lemma
says how to run it:

```toml
[ui]
command = "npm run dev -- --port {port}"   # started on a free port; or:
# static = "dist"                          # a directory telic serves (with build = "npm run build")
# url = "https://staging.example.com/"     # an app already running
viewports = ["390x844", "1280x800"]         # each explored separately
max_states = 300                            # budgets; hitting one leaves verdicts open
max_depth = 30
max_seconds = 600
workers = 1                                 # browsers per viewport (each takes one of TELIC_UI_SLOTS, default 2, machine-wide)
abstraction = "auto"                        # "controls", "screens", or auto: controls unless that exceeds 100 states
keys = ["Escape"]                           # keys a user may press anywhere
ignore = ['button "Sign out"']              # actions never fired (regexes)
text = "telic"                              # what is typed into text fields
fill = { "Coupon" = "SAVE10" }              # by field name (regex); emails, passwords, dates... are guessed
seed = false                                # true: an oracle proposes paths from the source first
```

Verdicts are cached in `.telic/ui.json` by the app's sources (every file
under the `telic.toml`'s directory except dependencies and build output),
the `[ui]` section, the lemma and telic's own UI code. `--no-ui` skips
running the app; cached verdicts still show. The web driver needs
`pip install 'telic[ui]'` and `playwright install chromium`.

## Spec expressions

Everything the code can say, plus:

| | Python | TypeScript | Rust |
|---|---|---|---|
| return value | `result` | `result` | `result` |
| entry value | `old(e)` | `old(e)` | `old(e)` |
| implication | `implies(a, b)` | `implies(a, b)` | `implies(a, b)` |
| for all / exists over a list | `all(p(x) for x in xs)`, `any(...)` | `xs.every(x => p(x))`, `xs.some(...)`, `xs.every((x, i) => ...)` | `xs.iter().all(\|x\| p(x))`, `.any(...)` |
| over an integer range | `all(p(i) for i in range(lo, hi))` | `range(lo, hi).every(i => p(i))` | `(lo..hi).all(\|i\| p(i))` |
| with index | `all(p(i, x) for i, x in enumerate(xs))` | `xs.every((x, i) => p(i, x))` | `(0..xs.len()).all(\|i\| p(i, xs[i]))` |
| filter | `all(p(x) for x in xs if q(x))` | `xs.every(x => !q(x) \|\| p(x))` | `xs.iter().all(\|x\| !q(x) \|\| p(x))` |
| sum / count | `sum(xs)`, `sum(xs[a:b])`, `xs.count(v)` | `sum(xs)`, `count(xs, v)`, `xs.reduce((a, b) => a + b, 0)` | `xs.iter().sum::<u64>()`, `.filter(...).count()` |
| membership | `v in xs` | `xs.includes(v)` | `xs.contains(&v)` |
| slices | `xs[a:b]`, `xs[-1]` | `xs.slice(a, b)`, `xs.at(-1)` | `xs[a..b]` |
| pure helpers | any loop-free, mutation-free function in the program, e.g. `ensures result == fib(n)` | same | same |

In Rust specs, arithmetic is mathematical (a spec never overflows) and
references dereference themselves (`x <= result` where `x: &i32`).

Spec expressions must themselves be well-defined: an index inside a spec is
checked like one in code.

## Types and semantics

**Numbers.** Python `int` is exact; `float` and JavaScript `number` are exact
rationals. `/` is real division; Python `//` floors and `%` takes the divisor's
sign; JavaScript `%` truncates; `round` rounds halves to even, `Math.round` rounds
them up. In TypeScript a `number` is an integer when telic can show it
(integer literals, `.length`, `Math.floor/…`, `Number.isInteger(p)` in a
`@requires`, or a `type int = number` alias).

**Objects.** Classes are references: two parameters may be the same object, and
counterexamples show it (`f(a=<Box v=0>, b=a)`). A class invariant (`#@ invariant`
in the class body, over `self`/`this` only) is assumed for objects passed in,
proved when they are handed back or passed on, and proved for any object a
function writes. Inside a loop, the objects written so far must satisfy it
after every iteration. A call changes only the fields the callee may write, and only
on objects it can reach. Dataclasses, pydantic models, TypeScript parameter
properties, getters and setters work as in the language.

**Inheritance.** A subclass of a checked class keeps its fields and invariants.
Calls go by the static type, so a call through a base may run any override: an
override without a contract inherits the one it overrides and is checked
against it, and a different contract is reported. An abstract method is its
contract; every override is checked against it. `super(...)`, `super.m()`
and a TypeScript subclass without a constructor run the base's code. Two
rules keep dispatch sound. An override assumes on entry only the subclass
invariants that code typed as the base cannot break (none over inherited
fields). A constructor may not hand `self` to other code while a subclass has
fields to set.

**Unions.** A TypeScript discriminated union (`{ kind: "a", ... } | { kind:
"b", ... }`) is a value whose tag is one of its literals. A field only some
variants have may be read only where the tag has been checked (`if`, `switch`,
`?:`, `&&`, `implies`, or an early `return`).

**Optionals.** `T | None`, `Optional[T]`, `T | undefined`, `x?: T`. Using an
optional where a value is needed (`x + 1`, `x.f`, `x!`) is an obligation that it
is present. Proving it uses whatever checks came before, so no narrowing syntax
is needed. `?.` and `??` work.

**Dicts and Maps.** `d[k]` / `m.get(k)!` must find the key. `get`, `in`/`has`,
assignment, `del`/`delete`, `keys()`/`values()`/`items()` and iteration are
modelled.

**Strings.** Concatenation, f-strings and template literals, `len`/`.length`,
`in`/`includes`, `startswith`, slicing, and comparison are exact (Z3's string
theory). Other methods (`lower()`, `replace`, …) are deterministic but
uninterpreted.

**Async.** At every `await`, other tasks may change any object that existed
before the call. They leave class invariants intact, but anything else is
re-checked. That is how a check-then-act race shows up. An async function
called without `await` has not finished when the call returns, so the call is
unchecked code: the caller learns nothing from its contract.

**Unchecked code.** A value telic knows nothing about (unannotated, `Any`,
`unknown`, a library type) is opaque. So is the result of a call into code it
doesn't check (a library, a decorated function, a local closure). Such a call:

- may change every list, dict or object it is handed;
- is assumed not to raise;
- leaves its result unconstrained.

Every such assumption is listed under *trusted base* in the report.

**Aliasing rules.** Lists and dicts are modelled as values. Binding a name to an
existing one (`ys = xs`) is rejected unless `xs` is never used again (a move);
otherwise copy it with `xs[:]` / `.slice()`. The same goes for storing one in a
field. A loop may not change the collection it iterates over.

**Strictness.** Falling off the end of a function that returns a value is an
error. A class name defined in two checked files is ambiguous: functions that
use it are reported unsupported until one is renamed. In TypeScript, `var` is rejected and a declaration may not shadow an
outer one. `x or default` / `x || default` are modelled with the language's
truthiness. Without a contract, telic only looks for crashes: termination and
intended raises are claims a contract makes.

**Rust.** Integers are their fixed width: every `+ - * /` on them must not
overflow, `/` and `%` truncate, and `as` wraps or saturates exactly as Rust
does. Indexing, slicing, `unwrap`/`expect`, `HashMap[&k]`, `panic!`,
`unreachable!` and `assert!` are panics to rule out. A value of an integer type
is known to be in its range. `Vec`, slices and arrays are lists; `Option` is an
optional; `HashMap` is a map; a non-`Copy` struct is an object (a move copies the
reference, so no alias survives it); a `Copy` struct of scalars is a record.
`&mut v` of a local list is `v` itself; a scalar behind `&mut` handed to a call
is unknown afterwards. `match`, `if let`, `while let`, `?` on `Option` (and on an
unchecked `Result`), shadowing, iterator chains (`map`, `filter`, `sum`,
`count`, `all`, `any`, `collect`) and C-like enums are modelled. Refutations are
replayed by compiling the file with `rustc` (overflow checks on) and calling the
function on the counterexample. Not yet modelled: data-carrying enums, tuple
structs, traits and generics (their values are opaque), and modules in other
files.
