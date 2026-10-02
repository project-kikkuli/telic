"""Verification corpus. The comment '# expect: STATUS' before each function is
the verdict telic must reach. 'refuted' means a counterexample confirmed by
running the code."""

import functools
from dataclasses import dataclass
from typing import Union


@dataclass(frozen=True)
class Item:
    price: int
    qty: int


# expect: proved
def abs_val(x: int) -> int:
    #@ ensures result >= 0
    #@ ensures result == x or result == -x
    if x < 0:
        return -x
    return x


# expect: refuted
def abs_bad(x: int) -> int:
    #@ ensures result >= 0
    if x < -1:
        return -x
    return x


# expect: proved
def max3(a: int, b: int, c: int) -> int:
    #@ ensures result >= a and result >= b and result >= c
    #@ ensures result == a or result == b or result == c
    m = a
    if b > m:
        m = b
    if c > m:
        m = c
    return m


# expect: proved
def sum_list(xs: list[int]) -> int:
    #@ ensures result == sum(xs)
    total = 0
    for x in xs:
        total += x
    return total


# expect: proved
def index_of(xs: list[int], target: int) -> int:
    #@ ensures -1 <= result < len(xs)
    #@ ensures implies(result >= 0, xs[result] == target)
    #@ ensures implies(result == -1, all(x != target for x in xs))
    #@ invariant all(xs[j] != target for j in range(i))
    for i in range(len(xs)):
        if xs[i] == target:
            return i
    return -1


# expect: proved
def count_matching(xs: list[int], v: int) -> int:
    #@ ensures result == xs.count(v)
    n = 0
    #@ invariant n == xs[:i].count(v)
    for i in range(len(xs)):
        if xs[i] == v:
            n += 1
    return n


# expect: proved
def fill(xs: list[int], v: int) -> None:
    #@ ensures len(xs) == len(old(xs))
    #@ ensures all(x == v for x in xs)
    #@ invariant all(xs[j] == v for j in range(i))
    for i in range(len(xs)):
        xs[i] = v


# expect: proved
def reverse_copy(xs: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    #@ ensures all(result[i] == xs[len(xs) - 1 - i] for i in range(len(xs)))
    out: list[int] = []
    #@ invariant len(out) == i
    #@ invariant all(out[j] == xs[len(xs) - 1 - j] for j in range(i))
    for i in range(len(xs)):
        out.append(xs[len(xs) - 1 - i])
    return out


# expect: proved
def order_total(items: list[Item]) -> int:
    #@ requires all(it.price >= 0 and it.qty >= 0 for it in items)
    #@ ensures result >= 0
    total = 0
    for it in items:
        total += it.price * it.qty
    return total


# expect: proved
def first_negative(xs: list[int]) -> int:
    #@ ensures implies(result >= 0, result < len(xs) and xs[result] < 0)
    i = 0
    found = -1
    while i < len(xs):
        if xs[i] < 0:
            found = i
            break
        i += 1
    return found


# expect: proved
def skip_zeros(xs: list[int]) -> int:
    #@ requires all(x >= 0 for x in xs)
    #@ ensures result >= 0
    n = 0
    for x in xs:
        if x == 0:
            continue
        n += x
    return n


# expect: proved
def safe_div(a: int, b: int) -> int:
    #@ raises b == 0
    #@ ensures result * b <= a < result * b + b or b < 0
    if b == 0:
        raise ValueError("division by zero")
    return a // b


# expect: refuted
def raises_wrongly(a: int) -> int:
    #@ raises a < 0
    if a <= 0:
        raise ValueError("bad")
    return a


# expect: proved
def clamp(x: int, lo: int, hi: int) -> int:
    #@ requires lo <= hi
    #@ ensures lo <= result <= hi
    #@ ensures implies(lo <= x <= hi, result == x)
    return max(lo, min(x, hi))


# expect: proved
def use_clamp(x: int) -> int:
    #@ ensures 0 <= result <= 100
    return clamp(x, 0, 100)


# expect: refuted
def bad_call(x: int) -> int:
    return clamp(x, 10, 0)


# expect: proved
def fib(n: int) -> int:
    #@ requires n >= 0
    #@ ensures result >= 0
    #@ decreases n
    if n < 2:
        return n
    return fib(n - 1) + fib(n - 2)


# expect: proved
def fib_iter(n: int) -> int:
    #@ requires n >= 0
    #@ ensures result == fib(n)
    a = 0
    b = 1
    #@ invariant a == fib(i) and b == fib(i + 1)
    for i in range(n):
        a, b = b, a + b
    return a


# expect: refuted
def mean_float(xs: list[float]) -> float:
    #@ requires len(xs) > 0
    #@ requires all(x >= 0 for x in xs)
    #@ ensures result >= 0
    return sum(xs) / len(xs)


# expect: proved
def mean_float_runtime_floats(xs: list[float]) -> float:
    #@ requires len(xs) > 0
    #@ requires all(x >= 0 for x in xs)
    #@ requires all(isinstance(x, float) for x in xs)
    #@ ensures result >= 0
    return sum(xs) / len(xs)


# expect: proved
def py_tag_identity(x: float) -> float:
    #@ requires isinstance(x, int)
    #@ ensures isinstance(result, int)
    return x


# expect: proved
def py_tag_call(x: float) -> float:
    #@ requires isinstance(x, int)
    #@ ensures isinstance(result, int)
    return py_tag_identity(x)


# expect: proved
def py_tag_index(xs: list[float]) -> float:
    #@ requires len(xs) > 0 and isinstance(xs[0], int)
    #@ ensures isinstance(result, int)
    return xs[0]


# expect: proved
def py_tag_comprehension(xs: list[float]) -> float:
    #@ requires len(xs) > 0 and isinstance(xs[0], int)
    #@ ensures isinstance(result, int)
    return [x for x in xs][0]


# expect: proved
def py_tag_concat(xs: list[float]) -> float:
    #@ requires len(xs) > 0 and isinstance(xs[0], int)
    #@ ensures isinstance(result, int)
    ys = xs + xs
    return ys[len(xs)]


# expect: proved
def py_tag_repeat(xs: list[float]) -> float:
    #@ requires len(xs) > 0 and isinstance(xs[0], int)
    #@ ensures isinstance(result, int)
    return ([xs[0]] * 2)[1]


# expect: proved
def py_tag_append(xs: list[float]) -> float:
    #@ requires len(xs) > 0 and isinstance(xs[0], int)
    #@ ensures isinstance(result, int)
    ys = xs.copy()
    ys.append(xs[0])
    return ys[len(xs)]


# expect: proved
def py_tag_filtered_comprehension(xs: list[float]) -> float:
    #@ requires len(xs) > 0 and isinstance(xs[0], int) and xs[0] >= 0
    #@ ensures isinstance(result, int)
    return [x for x in xs if x >= 0][0]


# expect: refuted
def python_min_preserves_first_nan(x: float) -> float:
    #@ requires x != x
    #@ ensures result == 1.0
    return min(x, 1.0)


# expect: refuted
def python_tagged_int_division_overflow() -> float:
    #@ ensures result == 0.0
    x: float = 10**400
    return x / 1


# expect: proved
def mixed_integer_cancellation_through_comprehension() -> float:
    #@ ensures result == 0.0
    n = 9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999
    xs = [n, -n, 0.0]
    return sum([x for x in xs])


# expect: refuted
def last_elem(xs: list[int]) -> int:
    return xs[len(xs)]


# expect: proved
def last_ok(xs: list[int]) -> int:
    #@ requires len(xs) > 0
    #@ ensures result == xs[-1]
    return xs[len(xs) - 1]


# expect: proved
def tail_sum(xs: list[int]) -> int:
    #@ requires len(xs) >= 1
    #@ ensures result == sum(xs) - xs[0]
    return sum(xs[1:])


# expect: proved
def contains(xs: list[int], v: int) -> bool:
    #@ ensures result == (v in xs)
    #@ invariant all(xs[j] != v for j in range(i))
    for i in range(len(xs)):
        if xs[i] == v:
            return True
    return False


# expect: proved
def status_label(paid: bool, shipped: bool) -> str:
    #@ ensures implies(shipped, result == "shipped")
    if shipped:
        return "shipped"
    if paid:
        return "paid"
    return "open"


# expect: refuted
def missing_return(x: int) -> int:
    if x > 0:
        return 1


# expect: proved
def countdown(n: int) -> int:
    #@ requires n >= 0
    #@ ensures result == 0
    while n > 0:
        n -= 1
    return n


# expect: open
def collatz_steps(n: int) -> int:
    #@ requires n >= 1
    steps = 0
    while n != 1:
        if n % 2 == 0:
            n = n // 2
        else:
            n = 3 * n + 1
        steps += 1
    return steps


# expect: refuted
def bad_invariant(n: int) -> int:
    #@ requires n >= 0
    s = 0
    #@ invariant s <= 10
    for i in range(n):
        s += 1
    return s


# expect: proved
def assert_ok(x: int) -> int:
    y = x * x
    #@ assert y >= 0
    return y


# expect: refuted
def assert_bad(x: int) -> int:
    y = x + 1
    assert y > x + 1
    return y


# expect: proved
def uses_dict(x: int) -> int:
    #@ ensures result == x
    d = {"a": x}
    return d["a"]


# expect: refuted
def uses_dict_missing(x: int) -> int:
    d = {"a": x}
    return d["b"]


# expect: proved
def swap_first_last(xs: list[int]) -> None:
    #@ requires len(xs) >= 2
    #@ ensures xs[0] == old(xs[len(xs) - 1]) and xs[len(xs) - 1] == old(xs[0])
    #@ ensures len(xs) == len(old(xs))
    t = xs[0]
    xs[0] = xs[len(xs) - 1]
    xs[len(xs) - 1] = t


# expect: proved
def call_mutator(ys: list[int]) -> int:
    #@ requires len(ys) >= 2
    #@ ensures result == old(ys[0])
    a = ys[0]
    swap_first_last(ys)
    return ys[len(ys) - 1]


# expect: proved
def is_sorted_check(xs: list[int]) -> bool:
    #@ ensures result == all(xs[i] <= xs[i + 1] for i in range(len(xs) - 1))
    #@ invariant all(xs[j] <= xs[j + 1] for j in range(i))
    for i in range(len(xs) - 1):
        if xs[i] > xs[i + 1]:
            return False
    return True


# expect: proved
def max_list(xs: list[int]) -> int:
    #@ requires len(xs) > 0
    #@ ensures all(x <= result for x in xs)
    #@ ensures result in xs
    m = xs[0]
    #@ invariant all(xs[j] <= m for j in range(i))
    #@ invariant m in xs
    for i in range(len(xs)):
        if xs[i] > m:
            m = xs[i]
    return m


# expect: proved
def sign(x: int) -> int:
    #@ ensures result == (1 if x > 0 else -1 if x < 0 else 0)
    if x > 0:
        return 1
    elif x < 0:
        return -1
    return 0


# expect: proved
def pymod(a: int, b: int) -> int:
    #@ requires b > 0
    #@ ensures 0 <= result < b
    return a % b


# expect: refuted
def pymod_neg(a: int, b: int) -> int:
    #@ requires b != 0
    #@ ensures 0 <= result
    return a % b


# expect: proved
def overloaded_format(x: float, n: int) -> int:
    #@ ensures result >= 0
    # the same formatting operation applied to a float and to an int
    return len(f"{x:>5}" + f"{n:>5}")


# expect: proved
def count_pairs(pairs: list[tuple[int, int]]) -> int:
    #@ ensures result == len(pairs)
    n = 0
    for a, b in pairs:
        #@ index i
        #@ invariant n == i
        n = n + 1
    return n


# expect: open
def first_of_last_pair(pairs: list[tuple[int, int]]) -> int:
    #@ ensures result >= 0
    t = 0
    for a, b in pairs:
        t = a
    return t


# expect: proved
def dict_put_pos(d: dict[str, int], k: str) -> None:
    #@ requires all(d[x] > 0 for x in d)
    #@ ensures all(d[x] > 0 for x in d)
    d[k] = 5


# expect: refuted
def dict_put_zero(d: dict[str, int], k: str) -> None:
    #@ requires all(d[x] > 0 for x in d)
    #@ ensures all(d[x] > 0 for x in d)
    d[k] = 0


# expect: proved
def dict_lookup_pos(d: dict[str, int], k: str) -> int:
    #@ requires all(d[x] > 0 for x in d)
    #@ ensures result >= 0
    if k in d:
        return d[k]
    return 0


# expect: open
def collatz_trail(n: int, out: list[int]) -> None:
    # no claim, but recursion that never ends raises RecursionError: crash-freedom needs termination
    if n <= 1:
        return
    out.append(n)
    collatz_trail(n // 2 if n % 2 == 0 else 3 * n + 1, out)


# expect: open
def claims_through_helper(n: int) -> int:
    #@ ensures result == 0
    return helper_without_claim(n)


def helper_without_claim(n: int) -> int:
    # its group makes a claim, so every edge of the cycle needs a measure
    if n == 0:
        return 0
    return claims_through_helper(n + 1)


class Wallet:
    #@ invariant self.cents >= 0

    def __init__(self):
        self.cents = 0


# expect: refuted
def empty_wallets(ws: list[Wallet]) -> None:
    for w in ws:
        w.cents = -1


# expect: proved
def fill_wallets(ws: list[Wallet], c: int) -> None:
    #@ requires c >= 0
    for i in range(len(ws)):
        if ws[i].cents < c:
            ws[i].cents = c


# expect: proved
def new_wallets(ws: list[Wallet], n: int) -> None:
    for i in range(n):
        w = Wallet()
        w.cents = 5
        ws.append(w)


class Span:
    #@ invariant self.lo <= self.hi

    def __init__(self):
        self.lo = 0
        self.hi = 0


# expect: refuted
def stretch(s: Span, x: int) -> None:
    #@ raises x < 0
    s.lo = s.hi + 1
    if x < 0:
        raise ValueError("negative")
    s.hi = s.lo


# expect: proved
def bump_wallets(ws: list[Wallet]) -> None:
    for w in ws:
        w.cents = w.cents + 1


# expect: proved
def total_cents(ws: list[Wallet]) -> int:
    #@ ensures result >= 0
    t = 0
    for w in ws:
        t += w.cents
    return t


# expect: proved
def top_up(book: dict[str, Wallet], who: str, c: int) -> None:
    #@ requires c >= 0
    if who in book:
        book[who].cents = book[who].cents + c


# Termination measures telic infers (none is written below).


# expect: proved
def count_down(n: int) -> int:
    #@ ensures result >= 0
    if n <= 0:
        return 0
    return 1 + count_down(n - 1)


# expect: proved
def count_to_minus_five(n: int) -> int:
    if n <= -5:
        return 0
    return count_to_minus_five(n - 1)


# expect: proved
def steps_up(i: int, hi: int) -> int:
    if i >= hi:
        return 0
    return 1 + steps_up(i + 1, hi)


# expect: proved
def str_steps(s: str) -> int:
    if s == "":
        return 0
    return 1 + str_steps(s[1:])


# expect: proved
def ackermann(m: int, n: int) -> int:
    #@ requires m >= 0 and n >= 0
    #@ ensures result >= 0
    if m == 0:
        return n + 1
    if n == 0:
        return ackermann(m - 1, 1)
    return ackermann(m - 1, ackermann(m, n - 1))


# expect: proved
def even_steps(n: int) -> bool:
    #@ requires n >= 0
    if n == 0:
        return True
    return odd_steps(n - 1)


# expect: proved
def odd_steps(n: int) -> bool:
    #@ requires n >= 0
    if n == 0:
        return False
    return even_steps(n - 1)


# expect: proved
def hand_off(n: int) -> int:
    # calls take_back with the same n: the measure is (n, rank in the group)
    if n <= 0:
        return 0
    return take_back(n)


# expect: proved
def take_back(n: int) -> int:
    #@ requires n >= 1
    return hand_off(n - 1)


@dataclass(frozen=True)
class Leaf:
    v: int


@dataclass(frozen=True)
class Fork:
    left: "Tree"
    right: "Tree"


Tree = Union[Leaf, Fork]


# expect: proved
def leaves(t: Tree) -> int:
    if isinstance(t, Leaf):
        return 1
    return leaves(t.left) + leaves(t.right)


@dataclass(frozen=True)
class Link:
    nxt: "Chain"


Chain = Union[Link, Leaf]


# expect: open
def chain_len(c: Chain) -> int:
    # knot() ties a Link to itself, so its depth is not finite; leaves() above keeps its proof
    if isinstance(c, Leaf):
        return 0
    return chain_len(c.nxt) + 1


# expect: proved
def knot() -> Link:
    link = Link(Leaf(0))
    object.__setattr__(link, "nxt", link)
    return link


# expect: open
def countdown_by_value(n: int) -> int:
    # terminates, but recursion through a function value has no measure telic can check
    #@ requires n >= 0
    f = countdown_by_value
    if n == 0:
        return 0
    return f(n - 1)


class Ticket:
    #@ lifecycle state: 0 -> 1 -> 2, 0 | 1 -> 3
    #@ lifecycle never state: 2 -> 0
    #@ lifecycle monotonic self.version
    #@ lifecycle once self.state == 2
    def __init__(self) -> None:
        self.state = 0
        self.version = 0


# expect: proved
def advance_ticket(t: Ticket) -> None:
    # every call keeps the lifecycle, so no sequence of calls reopens a closed ticket
    if t.state == 0 or t.state == 1:
        t.state = t.state + 1
        t.version = t.version + 1


# expect: proved
def cancel_twice(t: Ticket) -> None:
    # 0 -> 1 -> 3 in one call: a path in the lifecycle, so allowed
    if t.state == 0:
        t.state = 1
        t.state = 3


# expect: refuted
def reopen_ticket(t: Ticket) -> None:
    if t.state == 2:
        t.state = 0


# expect: refuted
def rewind_version(t: Ticket) -> None:
    t.version = t.version - 1


# expect: refuted
def restart_ticket(t: Ticket) -> None:
    # the initializer rebuilds the live ticket it runs on
    t.__init__()


# expect: proved
def advance_all(t: Ticket, u: Ticket) -> None:
    # callees keep the lifecycle, so their composition does
    advance_ticket(t)
    advance_ticket(u)
    advance_ticket(t)


# expect: refuted
def reopen_first(ts: list[Ticket]) -> None:
    # an object reached through a list: the runtime checks the objects in
    # a list parameter too, so the counterexample is confirmed
    if len(ts) > 0:
        t = ts[0]
        t.state = 0


# expect: proved
def no_flows_yet(n: int) -> list[Item]:
    #@ requires n >= 0
    #@ ensures all(sum(t.price for t in result if t.qty == m) == 0 for m in range(n))
    out: list[Item] = []
    return out


# expect: refuted
def flows_differ(xs: list[Item], n: int) -> int:
    #@ requires n >= 2
    #@ ensures all(sum(t.price for t in xs if t.qty == m) == 0 for m in range(n))
    return 0


# expect: refuted
def flows_by_member(xs: list[Item]) -> int:
    #@ requires all(sum(t.price for t in xs if t.qty == m) == m for m in range(3))
    #@ ensures sum(t.price for t in xs if t.qty == 2) == 1
    return 0


# expect: proved
def zero_balances(n: int) -> list[int]:
    #@ requires n >= 0
    #@ ensures len(result) == n
    #@ ensures sum(result) == 0
    return [0 for _ in range(n)]


# expect: proved
def zero_balances_rep(n: int) -> list[int]:
    #@ ensures len(result) == max(n, 0)
    #@ ensures sum(result) == 0
    return [0] * n


# expect: proved
def squares_upto(n: int) -> list[int]:
    #@ requires n >= 0
    #@ ensures all(result[i] == i * i for i in range(n))
    return [i * i for i in range(n)]


# expect: refuted
def alternating(n: int) -> list[int]:
    #@ requires n >= 1
    #@ ensures all(x == 0 for x in result)
    return [0, 1] * n


# Comprehensions: one 'for' over a list, range, enumerate or dict items is
# modelled; every shape keeps each element's obligations, under its 'if'.
def pos_int(x: int) -> int:
    #@ requires x > 0
    #@ ensures result == x
    return x


# expect: proved
def comp_range_index(xs: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    #@ ensures all(result[i] == xs[i] + 1 for i in range(len(xs)))
    return [xs[i] + 1 for i in range(len(xs))]


# expect: proved
def comp_guarded_div(xs: list[int]) -> list[int]:
    #@ ensures len(result) <= len(xs)
    return [10 // x for x in xs if x != 0]


# expect: proved
def comp_guarded_call(xs: list[int]) -> list[int]:
    #@ ensures len(result) <= len(xs)
    return [pos_int(x) for x in xs if x > 0]


# expect: refuted
def comp_unguarded_call(xs: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    return [pos_int(x) for x in xs]


# expect: proved
def comp_items(d: dict[str, int]) -> int:
    #@ ensures result == 0
    _ = {k: v + 1 for k, v in d.items()}
    return 0


# expect: proved
def comp_enumerate(xs: list[int]) -> list[int]:
    #@ ensures len(result) == len(xs)
    return [x + i for i, x in enumerate(xs)]


# expect: proved
def comp_nested_guarded(xs: list[int], ys: list[int]) -> int:
    #@ ensures result == 0
    _ = [a // b for a in xs for b in ys if b > 0]
    return 0


# expect: refuted
def comp_nested_div(xs: list[int], ys: list[int]) -> int:
    #@ ensures result == 0
    _ = [a // b for a in xs for b in ys]
    return 0


# expect: proved
def gen_guarded_sum(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = sum(10 // x for x in xs if x > 0)
    return 0


# expect: proved
def set_guarded_call(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = {pos_int(x) for x in xs if x >= 1}
    return 0


# expect: proved
def pay_member(xs: list[Item], m: int, p: int) -> list[Item]:
    # a filtered sum over a list that grows by append
    #@ ensures sum(t.price for t in result if t.qty == m) == sum(t.price for t in xs if t.qty == m) + p
    out = xs[:]
    out.append(Item(p, m))
    return out


# expect: refuted
def pay_member_lost(xs: list[Item], m: int, p: int) -> list[Item]:
    #@ ensures sum(t.price for t in result if t.qty == m) == sum(t.price for t in xs if t.qty == m)
    out = xs[:]
    out.append(Item(p, m))
    return out


# expect: proved
def paid_each(n: int, k: int) -> list[Item]:
    # per-member filtered sums kept by a loop that appends
    #@ requires n >= 1 and k >= 0
    #@ ensures all(sum(t.price for t in result if t.qty == m) == (k if m == 0 else 0) for m in range(n))
    out: list[Item] = []
    c = 0
    while c < k:
        #@ invariant 0 <= c <= k
        #@ invariant all(sum(t.price for t in out if t.qty == m) == (c if m == 0 else 0) for m in range(n))
        out.append(Item(1, 0))
        c += 1
    return out


# expect: proved
def cleared(rest: list[int], i: int) -> bool:
    # non-negatives summing to zero are all zero
    #@ requires sum(rest) == 0 and i == len(rest)
    #@ requires all(rest[k] >= 0 for k in range(i))
    #@ ensures all(rest[m] == 0 for m in range(len(rest)))
    return True


# expect: proved
def parse_digits(s: str) -> int:
    #@ requires s == "-42"
    #@ ensures result == -42
    return int(s)


# expect: refuted
def parse_unchecked(s: str) -> int:
    # int() raises ValueError on text it cannot parse
    #@ ensures result >= 0 or result < 0
    return int(s)


# expect: proved
def parse_or_zero(s: str) -> int:
    #@ ensures True
    try:
        return int(s)
    except ValueError:
        return 0


# expect: proved
def parse_float_digits(s: str) -> float:
    #@ requires s == "3"
    #@ ensures result == 3.0
    return float(s)


def _counts_total(xs: list[int]) -> int:
    #@ requires all(x >= 0 for x in xs)
    #@ ensures result >= 0
    out = 0
    for x in xs:
        #@ invariant out >= 0
        out += x
    return out


# expect: proved
def counts_from_json(body: dict) -> int:
    # untyped JSON checked with isinstance, then handed to a contracted function
    xs = body["xs"]
    if not isinstance(xs, list) or not all(isinstance(x, int) and x >= 0 for x in xs):
        raise ValueError("xs must be a list of counts")
    return _counts_total(xs)


# expect: proved
def items_from_json(body: dict, n: int) -> list[Item]:
    # objects built from JSON keep what the loop says of them across
    # unchecked calls: the function hands none of them out
    #@ requires n >= 0
    #@ ensures all(t.qty == n for t in result)
    out: list[Item] = []
    for e in body["items"]:
        #@ invariant all(t.qty == n for t in out)
        price = int(e["price"])
        out.append(Item(price, n))
    return out



# -- library functions that run a callback on each element --------------------


# expect: proved
def keyed_guarded(xs: list[int]) -> int:
    #@ requires all(x > 0 for x in xs)
    #@ ensures result == 0
    _ = sorted(xs, key=lambda x: 10 // x)
    _ = max(xs, key=lambda x: 10 // x) if xs else 0
    xs.sort(key=lambda x: 10 // x)
    return 0


# expect: refuted
def sorted_key_div(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = sorted(xs, key=lambda x: 10 // x)
    return 0


# expect: refuted
def min_key_div(xs: list[int]) -> int:
    #@ requires len(xs) > 0
    #@ ensures result == 0
    _ = min(xs, key=lambda x: 10 // x)
    return 0


# expect: refuted
def list_sort_key_div(xs: list[int]) -> int:
    #@ ensures result == 0
    xs.sort(key=lambda x: 10 // x)
    return 0


# expect: proved
def map_filter_guarded(xs: list[int]) -> int:
    #@ requires all(x >= 1 for x in xs)
    #@ ensures result == 0
    _ = list(map(pos_int, xs))
    _ = list(filter(lambda x: 10 // x > 1, xs))
    _ = list(map(lambda x: pos_int(x) + 1, xs))
    return 0


# expect: refuted
def map_named_unguarded(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = list(map(pos_int, xs))
    return 0


# expect: refuted
def filter_div(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = list(filter(lambda x: 10 // x > 1, xs))
    return 0


# expect: proved
def reduce_guarded(xs: list[int]) -> int:
    #@ requires all(x > 0 for x in xs)
    #@ ensures result == 0
    _ = functools.reduce(lambda acc, x: acc + 10 // x, xs, 0)
    return 0


# expect: refuted
def reduce_div(xs: list[int]) -> int:
    #@ ensures result == 0
    _ = functools.reduce(lambda acc, x: acc + 10 // x, xs, 0)
    return 0
