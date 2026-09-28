"""Referral bonuses double at every level of the referral tree."""

#@ intent BONUS-COMPOSE: WHEN two referral paths are chained, the shop shall pay
#@   the product of their bonuses.
#@   by: chained_bonus_is_product


def level_bonus(depth: int) -> int:
    #@ requires depth >= 0
    #@ ensures result >= 1
    #@ decreases depth
    if depth == 0:
        return 1
    return 2 * level_bonus(depth - 1)


def chained_bonus_is_product(a: int, b: int) -> bool:
    #@ requires a >= 0 and b >= 0
    #@ intent BONUS-COMPOSE
    #@ ensures result
    return level_bonus(a + b) == level_bonus(a) * level_bonus(b)
