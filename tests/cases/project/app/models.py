from enum import Enum

FEE_CENTS = 30


class Status(Enum):
    OPEN = 1
    PAID = 2


class Invoice:
    #@ invariant self.amount >= 0
    #@ invariant self.paid <= self.amount

    def __init__(self, amount: int):
        #@ requires amount >= 0
        #@ ensures self.amount == amount and self.paid == 0
        self.amount = amount
        self.paid: int = 0
        self.status: Status = Status.OPEN

    def pay(self, cents: int) -> None:
        #@ requires 0 < cents <= self.amount - self.paid
        #@ ensures self.paid == old(self.paid) + cents
        self.paid += cents
        if self.paid == self.amount:
            self.status = Status.PAID


def fee(amount: int) -> int:
    #@ requires amount >= 0
    #@ ensures result >= FEE_CENTS
    return amount // 100 + FEE_CENTS
