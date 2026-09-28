from dataclasses import dataclass
from typing import Optional


class Account:
    #@ invariant self.balance >= 0
    #@ invariant self.limit >= 0

    def __init__(self, owner: str, limit: int = 100):
        #@ requires limit >= 0
        #@ ensures self.balance == 0 and self.owner == owner
        self.owner = owner
        self.balance: int = 0
        self.limit = limit

    def deposit(self, amount: int) -> None:
        #@ requires amount > 0
        #@ ensures self.balance == old(self.balance) + amount
        self.balance += amount

    def withdraw(self, amount: int) -> bool:
        #@ requires amount > 0
        #@ ensures implies(result, self.balance == old(self.balance) - amount)
        if amount > self.balance:
            return False
        self.balance -= amount
        return True

    def bad_withdraw(self, amount: int) -> None:
        self.balance -= amount


def transfer(a: Account, b: Account, amount: int) -> bool:
    #@ requires amount > 0
    #@ ensures implies(result, a.balance + b.balance == old(a.balance + b.balance))
    if a.withdraw(amount):
        b.deposit(amount)
        return True
    return False


def find(accounts: dict[str, int], name: str) -> Optional[int]:
    #@ ensures implies(result is not None, name in accounts)
    if name in accounts:
        return accounts[name]
    return None


def total(x: Optional[int], y: int) -> int:
    return x + y


def safe_total(x: Optional[int], y: int = 1) -> int:
    if x is None:
        return y
    return x + y


def lookup(d: dict[str, int], k: str) -> int:
    return d[k]


def open_account(name: str) -> Account:
    #@ ensures result.balance == 0
    a = Account(name)
    a.deposit(5)
    return a
