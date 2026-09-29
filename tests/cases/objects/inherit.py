from pydantic import BaseModel


class Account:
    #@ invariant self.balance >= 0
    def __init__(self, owner: str, balance: int):
        #@ requires balance >= 0
        self.owner = owner
        self.balance = balance

    def deposit(self, amount: int) -> None:
        #@ requires amount > 0
        #@ ensures self.balance == old(self.balance) + amount
        self.balance += amount

    def withdraw(self, amount: int) -> int:
        #@ requires 0 < amount
        #@ ensures result <= amount
        #@ ensures self.balance == old(self.balance) - result
        taken = min(amount, self.balance)
        self.balance -= taken
        return taken


class Savings(Account):
    #@ invariant self.rate >= 0
    def __init__(self, owner: str, balance: int, rate: int):
        #@ requires balance >= 0 and rate >= 0
        self.owner = owner
        self.balance = balance
        self.rate = rate

    def add_interest(self) -> None:
        #@ ensures self.balance >= old(self.balance)
        self.balance += self.balance * self.rate // 100


class Capped(Account):
    # no contract: inherits Account.withdraw's, and is checked against it
    def withdraw(self, amount: int) -> int:
        taken = min(amount, self.balance, 100)
        self.balance -= taken
        return taken


class Leaky(Account):
    # breaks the inherited '@ensures result <= amount'
    def withdraw(self, amount: int) -> int:
        self.balance -= 0
        return amount + 1


def savings_deposit(s: Savings) -> int:
    #@ ensures result > old(s.balance)
    s.deposit(5)  # inherited method, runs on a Savings
    return s.balance


def through_base(a: Account) -> int:
    #@ ensures result <= 10
    return a.withdraw(10)  # may run Capped.withdraw or Leaky.withdraw


class RWModel(BaseModel):
    pass


class Article(RWModel):
    title: str
    likes: int = 0


def new_article(title: str) -> Article:
    #@ ensures result.likes == 0
    return Article(title=title)


def liked(a: Article) -> int:
    #@ ensures result == a.likes + 1
    return a.likes + 1
