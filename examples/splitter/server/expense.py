from dataclasses import dataclass
from enum import Enum


class Status(Enum):
    DRAFT = "draft"
    POSTED = "posted"
    SETTLED = "settled"


class ExpenseError(Exception):
    pass


@dataclass
class Expense:
    payer: int
    amount: int
    shares: list[int]
    status: Status

    #@ invariant self.amount >= 0
    #@ invariant sum(self.shares) == self.amount
    #@ invariant all(s >= 0 for s in self.shares)
    #@ invariant 0 <= self.payer < len(self.shares)
    #@ [EXPENSE-LIFECYCLE] lifecycle status: Status.DRAFT -> Status.POSTED -> Status.SETTLED
    #@ [EXPENSE-LIFECYCLE] lifecycle never status: Status.SETTLED -> Status.DRAFT
    #@ [EXPENSE-LIFECYCLE] lifecycle never status: Status.POSTED -> Status.DRAFT
    #@ [EXPENSE-LIFECYCLE] lifecycle never status: Status.SETTLED -> Status.POSTED

    def edit(self, payer: int, amount: int, shares: list[int]) -> None:
        #@ raises self.status != Status.DRAFT
        #@ requires amount >= 0
        #@ requires sum(shares) == amount
        #@ requires all(s >= 0 for s in shares)
        #@ requires 0 <= payer < len(shares)
        if self.status != Status.DRAFT:
            raise ExpenseError("only a draft can be edited")
        self.payer = payer
        self.amount = amount
        self.shares = shares[:]

    def post(self) -> None:
        #@ raises self.status != Status.DRAFT
        #@ ensures self.status == Status.POSTED
        if self.status != Status.DRAFT:
            raise ExpenseError("only a draft can be posted")
        self.status = Status.POSTED

    def settle(self) -> None:
        #@ raises self.status != Status.POSTED
        #@ ensures self.status == Status.SETTLED
        if self.status != Status.POSTED:
            raise ExpenseError("only a posted expense can be settled")
        self.status = Status.SETTLED


def new_expense(payer: int, amount: int, shares: list[int]) -> Expense:
    #@ requires amount >= 0
    #@ requires sum(shares) == amount
    #@ requires all(s >= 0 for s in shares)
    #@ requires 0 <= payer < len(shares)
    #@ ensures result.status == Status.DRAFT
    return Expense(payer, amount, shares[:], Status.DRAFT)
