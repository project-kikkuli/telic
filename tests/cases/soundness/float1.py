# Floats are IEEE doubles: rounding, NaN, infinities, -0.0 and int/float mixing.
import math


#@ ensures result
def classic() -> bool:
    return 0.1 + 0.2 == 0.3


#@ ensures result == x
def reflexive(x: float) -> float:
    return x


#@ requires x == 0.0
#@ ensures result == 1.0
def neg_zero(x: float) -> float:
    return math.copysign(1.0, x)


#@ ensures result == 1.0
def zero_sign(x: float) -> float:
    return 1.0 / (x * 0.0 + 1.0)


#@ ensures result > x
def grows(x: float) -> float:
    return x + 1.0


#@ ensures result == n + 1
def big_int(n: int) -> float:
    return float(n) + 1.0


#@ ensures result
def exact_compare() -> bool:
    return 9007199254740993 == float(9007199254740993)


#@ ensures result < 1e308 * 10
def overflow(x: float) -> float:
    return x * 10.0


#@ requires x >= 0.0
#@ ensures result >= 0
def to_int(x: float) -> int:
    return math.floor(x)


#@ requires b != 0
#@ ensures result == a
def cents(a: int, b: int) -> float:
    return a / b * b


#@ requires math.isfinite(x) and math.isfinite(y)
#@ ensures result == (y + x) + 1.0
def order(x: float, y: float) -> float:
    return (x + 1.0) + y


#@ ensures result == [x]
def held(x: float) -> list[float]:
    return [x + 0.0]


#@ requires math.isfinite(x)
#@ ensures result >= x
def fine(x: float) -> float:
    return abs(x) if x >= 0.0 else x
