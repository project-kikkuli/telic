"""Verification corpus. The comment '# expect: STATUS' before each function is
the verdict telic must reach. 'refuted' means a counterexample confirmed by
running the code."""

from dataclasses import dataclass


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


# expect: proved
def mean_float(xs: list[float]) -> float:
    #@ requires len(xs) > 0
    #@ requires all(x >= 0 for x in xs)
    #@ ensures result >= 0
    return sum(xs) / len(xs)


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


# expect: proved
def collatz_trail(n: int, out: list[int]) -> None:
    # no claim and not a logical definition: only crash-freedom is checked, as for loops
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
