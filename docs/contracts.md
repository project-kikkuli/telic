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
| `requires`, `ensures`, `decreases`, `raises`, `intent`, `mirrors`, `trusted` | a function | contiguous comment lines directly above the `def`/`function`, or the first lines of its body |
| `invariant`, `decreases`, `index` | a loop | directly above the loop header, or the first lines of its body |
| `assert`, `assume` | a statement position | anywhere inside a block |
| `intent ID: sentence` | the module | anywhere outside a function |

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
treated the same way.

**`assume P`** is assumed without proof. It's an escape hatch and is listed in
every report under *trusted base*.

**`trusted`**: the function's contract is assumed and its body not verified
(FFI, performance hacks). Also listed under *trusted base*.

## Intents

An intent is a top-level requirement, written for a reviewer as one EARS
sentence. It is not a formula, and telic never reports one as "proved".

```python
#@ intent REFUND-CAP: WHEN a refund is requested, the shop shall refund at most
#@   what the customer paid, net of earlier refunds.
#@   by: refund_amount, Ledger.apply, web/checkout.ts::refundButton
```

Declare an intent anywhere in the project; IDs are `UPPER-KEBAB` and unique
project-wide. What telic proves are **lemmas** one layer below: contract clauses
that cite the intent. `#@ intent ID` inside a function tags every following
clause, and `#@ [ID] ensures …` tags one clause. An intent's lemmas can be spread
over many functions, files and both languages, and an `@mirrors` equivalence
counts as a lemma too.

**Two-sided links.** `by:` points down from the intent to the functions that
back it, and citations point back up. telic checks both directions: a `by:` entry
that does not cite the intent, or a function that cites it without being listed,
is reported, and `telic intents` fails on it. `by:` accepts `name`,
`Class.method` or `path::name`.

**EARS.** The sentence is linted against the EARS patterns:
`The <system> shall …`, `WHEN <trigger>, the <system> shall …`, `WHILE …`,
`IF … THEN …`, `WHERE …`, and combinations of them. One `shall`, one sentence.

**Status** says what the lemmas establish:

`backed` (every lemma proved) · `broken` (a lemma refuted) · `partial` (some
open) · `unbacked` (declared, nothing cites it) · `undeclared` (cited, never
declared).

**Coverage** is a separate question: do the lemmas cover the requirement? A
prover can't answer it, so telic records an answer instead:

```
telic intents --accept REFUND-CAP      # you reviewed it: pinned to a digest of
                                       # the sentence and the lemma set
telic intents --judge                  # a cheap model's opinion, cached by the same
                                       # digest, always labelled "judged"
```

A review goes stale when either the sentence or the lemma set changes. The
judge reads `ANTHROPIC_API_KEY` (model: `TELIC_JUDGE_MODEL`, default a Haiku
model), or `TELIC_JUDGE_CMD`, any command that reads the prompt on stdin.

## Mirrors

```ts
//@ mirrors ../server/pricing.py::quote
```

The path is relative to the declaring file; the named file is loaded
automatically. The two functions must take the same number of parameters (matched
by position) and must agree on every input both preconditions accept. An `int`
parameter against a `number` parameter is compared on integers.

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
function writes. A call changes only the fields the callee may write, and only
on objects it can reach. Dataclasses, pydantic models, TypeScript parameter
properties, getters and setters work as in the language.

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
re-checked. That is how a check-then-act race shows up.

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
error. In TypeScript, `var` is rejected and a declaration may not shadow an
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
function on the counterexample.
