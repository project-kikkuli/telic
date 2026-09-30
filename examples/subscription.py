"""Subscription billing: a lifecycle proved across every call, not tested.

`telic check examples/subscription.py` proves each method keeps the
lifecycles below; together they rule out any sequence of calls that
reactivates a cancelled subscription or un-charges a customer.
"""

from enum import Enum

#@ aim CANCEL-FINAL: WHILE a subscription is cancelled, the billing system shall never reactivate it.
#@   by: Subscription
#@ aim CHARGES-KEPT: The billing system shall never reduce what a subscriber has been charged or refunded.
#@   by: Subscription


class State(Enum):
    TRIAL = 1
    ACTIVE = 2
    PAST_DUE = 3
    CANCELLED = 4


class Subscription:
    #@ invariant self.price > 0
    #@ invariant 0 <= self.refunded <= self.charged
    #@ lifecycle state: State.TRIAL -> State.ACTIVE -> State.PAST_DUE -> State.ACTIVE,
    #@   State.TRIAL | State.ACTIVE | State.PAST_DUE -> State.CANCELLED
    #@ [CANCEL-FINAL] lifecycle once self.state == State.CANCELLED
    #@ [CANCEL-FINAL] lifecycle never state: State.CANCELLED -> State.ACTIVE
    #@ [CHARGES-KEPT] lifecycle monotonic self.charged
    #@ [CHARGES-KEPT] lifecycle monotonic self.refunded

    def __init__(self, price: int):
        #@ requires price > 0
        self.state = State.TRIAL
        self.price = price
        self.charged = 0
        self.refunded = 0

    def activate(self) -> None:
        if self.state == State.TRIAL:
            self.state = State.ACTIVE

    def renew(self, card_ok: bool) -> None:
        if self.state == State.ACTIVE or self.state == State.PAST_DUE:
            if card_ok:
                self.charged = self.charged + self.price
                self.state = State.ACTIVE
            else:
                self.state = State.PAST_DUE

    def refund(self, amount: int) -> int:
        #@ requires amount >= 0
        #@ ensures 0 <= result <= amount
        give = min(amount, self.charged - self.refunded)
        self.refunded = self.refunded + give
        return give

    def cancel(self) -> None:
        self.state = State.CANCELLED


def settle(sub: Subscription, card_ok: bool) -> None:
    """A billing run: renew, and cancel what still cannot pay."""
    sub.renew(card_ok)
    if sub.state == State.PAST_DUE and not card_ok:
        sub.cancel()
