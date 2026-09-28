# Contract reference

A contract line is a line comment starting with `#@` (Python) or `//@`
(TypeScript), followed by a keyword. The payload is an expression in the host
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
holds. Without `@raises`, any reachable `raise` is an error.

**`assert P`** is proved statically, then assumed. Native `assert` statements are
treated the same way.

**`assume P`** is assumed without proof. It's an escape hatch and is listed in
every report under *trusted base*.

**`trusted`**: the function's contract is assumed and its body not verified
(FFI, performance hacks). Also listed under *trusted base*.

## Intents

```python
#@ intent REFUND-CAP: A refund never exceeds what the customer paid, net of earlier refunds.
```

declares an intent (IDs are `UPPER-KEBAB`). Inside a function, `#@ intent ID`
links the function and tags every following clause, until the next `intent`
line. `#@ [ID] ensures …` tags a single clause. An intent's status is derived
from the evidence of every function linked to it, plus any `@mirrors` it covers:

`proved` · `refuted` · `open` · `unformalized` (declared, no clause carries it) ·
`undeclared` (referenced, never declared).

The EARS patterns (`WHEN <trigger> the <system> shall <response>`, `IF …
THEN …`, `WHILE …`) make good intent sentences: one sentence, one requirement.

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

| | Python | TypeScript |
|---|---|---|
| return value | `result` | `result` |
| entry value | `old(e)` | `old(e)` |
| implication | `implies(a, b)` | `implies(a, b)` |
| for all / exists over a list | `all(p(x) for x in xs)`, `any(...)` | `xs.every(x => p(x))`, `xs.some(...)`, `xs.every((x, i) => ...)` |
| over an integer range | `all(p(i) for i in range(lo, hi))` | `range(lo, hi).every(i => p(i))` |
| with index | `all(p(i, x) for i, x in enumerate(xs))` | `xs.every((x, i) => p(i, x))` |
| filter | `all(p(x) for x in xs if q(x))` | `xs.every(x => !q(x) \|\| p(x))` |
| sum / count | `sum(xs)`, `sum(xs[a:b])`, `xs.count(v)` | `sum(xs)`, `count(xs, v)`, `xs.reduce((a, b) => a + b, 0)` |
| membership | `v in xs` | `xs.includes(v)` |
| slices | `xs[a:b]`, `xs[-1]` | `xs.slice(a, b)`, `xs.at(-1)` |
| pure helpers | any loop-free, mutation-free function in the program, e.g. `ensures result == fib(n)` | same |

Spec expressions must themselves be well-defined: an index inside a spec is
checked like one in code.

## Types and semantics

**Python.** Parameters need annotations: `int`, `float`, `bool`, `str`,
`list[T]` (also `List[T]`, `Sequence[T]`), and `@dataclass(frozen=True)` /
`NamedTuple` records. `int` is exact. `float` is an exact rational. `/` is real
division, `//` floors, `%` takes the divisor's sign, `round` rounds halves to
even, `int(x)` truncates, and negative indices wrap.

**TypeScript.** `number` is an exact rational unless telic can show it's an
integer: integer literals, `.length`, `Math.floor/ceil/trunc/round`, integer
`+ - * %`, parameters whose contract says `Number.isInteger(p)`, and parameters
typed with an alias named `int` (`type int = number`). For locals and return
values, integrality is inferred. `/` is real division, `%` truncates (takes the
dividend's sign), `Math.round` rounds halves up, and `Math.floor(a / b)` on
integers is floor division. Reading `xs[i]` out of bounds (which JavaScript
silently turns into `undefined`) is an error. Interfaces and object type aliases
with scalar fields are records. `as` and `!` are rejected: they hide exactly
what telic checks.

**Both.** Lists are values. Binding a name to an existing list (`ys = xs`,
`ys = xs if c else zs`, `ys, k = xs, 0`) would create an alias the model can't
track, so it's rejected. Only a fresh list (a literal, a slice copy, or a call
result) can be bound. Copy with `xs[:]` / `xs.slice()`. A function may not
return one of its list parameters, and the same list may not be passed twice to
a function that mutates a list parameter. A loop may not iterate over a list
that its body changes, directly or through a call.

`a or b` / `a || b` must have boolean operands when used as a value, because
both languages return an operand there, not a boolean. In a condition,
truthiness applies as usual. A variable that is assigned on only some paths
cannot be read afterwards. Builtins rebound in the module (`def abs(...)`,
`from x import round`) are not treated as builtins. Records must be immutable
(`@dataclass(frozen=True)` without custom dunder methods, or `NamedTuple`).

In TypeScript, `var` is rejected (use `let`/`const`), a declaration may not
shadow an outer variable, and `const` bindings cannot be reassigned. Only a
top-level conjunct `Number.isInteger(p)` of a `@requires` makes `p` an
integer. Distinct list arguments are assumed not to alias. A callee that
mutates a list parameter is modelled at the call site: the argument gets fresh
contents constrained by the callee's `@ensures` (with `old`). `print` and
`console.*` are ignored.
