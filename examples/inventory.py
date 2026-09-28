"""Warehouse inventory rules: a realistic vibecoded module, fully contracted."""

from dataclasses import dataclass

#@ intent STOCK-NONNEG: Stock levels never go negative.
#@ intent RESERVE-BOUNDED: WHEN an order is reserved the system shall reserve no more than is in stock.
#@ intent RESTOCK-ALERT: IF stock falls below the reorder point THEN the item shall be flagged for restock.


@dataclass(frozen=True)
class Sku:
    on_hand: int
    reserved: int
    reorder_point: int


def available(s: Sku) -> int:
    #@ requires 0 <= s.reserved <= s.on_hand
    #@ ensures 0 <= result <= s.on_hand
    return s.on_hand - s.reserved


def reserve(s: Sku, qty: int) -> Sku:
    #@ requires 0 <= s.reserved <= s.on_hand and qty >= 0
    #@ intent RESERVE-BOUNDED
    #@ ensures result.reserved <= result.on_hand
    #@ ensures result.on_hand == s.on_hand
    #@ ensures result.reserved - s.reserved == min(qty, s.on_hand - s.reserved)
    take = min(qty, available(s))
    return Sku(on_hand=s.on_hand, reserved=s.reserved + take, reorder_point=s.reorder_point)


def needs_restock(s: Sku) -> bool:
    #@ requires 0 <= s.reserved <= s.on_hand
    #@ intent RESTOCK-ALERT
    #@ ensures result == (s.on_hand - s.reserved < s.reorder_point)
    return available(s) < s.reorder_point


def restock_list(skus: list[Sku]) -> list[int]:
    #@ requires all(0 <= s.reserved <= s.on_hand for s in skus)
    #@ intent RESTOCK-ALERT
    #@ ensures all(0 <= i < len(skus) for i in result)
    #@ ensures all(needs_restock(skus[i]) for i in result)
    out: list[int] = []
    #@ invariant all(0 <= j < i for j in out)
    #@ invariant all(needs_restock(skus[j]) for j in out)
    for i in range(len(skus)):
        if needs_restock(skus[i]):
            out.append(i)
    return out


def ship(levels: list[int], idx: int, qty: int) -> None:
    #@ requires 0 <= idx < len(levels)
    #@ requires all(x >= 0 for x in levels)
    #@ requires 0 <= qty <= levels[idx]
    #@ intent STOCK-NONNEG
    #@ ensures all(x >= 0 for x in levels)
    #@ ensures len(levels) == len(old(levels))
    #@ ensures levels[idx] == old(levels[idx]) - qty
    levels[idx] -= qty


def total_units(levels: list[int]) -> int:
    #@ requires all(x >= 0 for x in levels)
    #@ ensures result >= 0
    #@ ensures result == sum(levels)
    return sum(levels)
