"""Billing rules for the shop. Written fast, by an AI, at 2am. No tests."""

from dataclasses import dataclass

#@ intent REFUND-CAP: WHEN a refund is requested, the shop shall refund at most
#@   what the customer paid, net of earlier refunds.
#@   by: refund_amount
#@ intent ORDER-NONNEG: The shop shall never compute a negative order total.
#@   by: order_total


@dataclass(frozen=True)
class LineItem:
    unit_cents: int
    quantity: int


def refund_amount(paid: int, refunded: int, requested: int) -> int:
    """How much of `requested` (in cents) we can refund right now."""
    #@ requires 0 <= refunded <= paid
    #@ requires requested >= 0
    #@ intent REFUND-CAP
    #@ ensures 0 <= result <= paid - refunded
    if requested > paid:
        return paid - refunded
    return requested


def order_total(items: list[LineItem]) -> int:
    """Sum of line items, in cents."""
    #@ requires all(it.unit_cents >= 0 and it.quantity >= 0 for it in items)
    #@ intent ORDER-NONNEG
    #@ ensures result >= 0
    total = 0
    for it in items:
        total += it.unit_cents * it.quantity
    return total


def discounted_total(subtotal: int, percent: int) -> int:
    """Subtotal after a percentage discount, in whole cents."""
    #@ requires subtotal >= 0 and 0 <= percent <= 100
    #@ intent PRICE-AGREE
    #@ ensures 0 <= result <= subtotal
    return subtotal - round(subtotal * percent / 100)
