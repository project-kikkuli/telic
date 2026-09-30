from dataclasses import dataclass

from expense import Expense, Status

#@ aim SETTLE-CLEARS: WHEN a group settles up, the splitter shall propose positive payments
#@   from members who owe to members who are owed that clear every balance.
#@   by: settle_up


@dataclass
class Transfer:
    debtor: int
    creditor: int
    amount: int


def apply_expense(balances: list[int], payer: int, amount: int, shares: list[int]) -> list[int]:
    #@ aim BALANCE-ZERO
    #@ requires len(shares) == len(balances)
    #@ requires 0 <= payer < len(balances)
    #@ requires sum(shares) == amount
    #@ ensures len(result) == len(balances)
    #@ ensures sum(result) == sum(balances)
    out = balances[:]
    out[payer] = out[payer] + amount
    for i in range(len(out)):
        #@ invariant len(out) == len(balances)
        #@ invariant sum(out) == sum(balances) + amount - sum(shares[:i])
        out[i] = out[i] - shares[i]
    return out


def balances(members: int, expenses: list[Expense]) -> list[int]:
    #@ aim BALANCE-ZERO
    #@ requires members >= 1
    #@ requires all(len(e.shares) == members for e in expenses)
    #@ ensures len(result) == members
    #@ ensures sum(result) == 0
    out = [0] * members
    for e in expenses:
        #@ invariant len(out) == members
        #@ invariant sum(out) == 0
        if e.status == Status.POSTED:
            out = apply_expense(out, e.payer, e.amount, e.shares)
    return out


def settle_up(balances: list[int]) -> list[Transfer]:
    #@ aim SETTLE-CLEARS
    #@ requires sum(balances) == 0
    #@ ensures all(t.amount > 0 for t in result)
    #@ ensures all(0 <= t.debtor < len(balances) and 0 <= t.creditor < len(balances) for t in result)
    #@ ensures all(balances[t.debtor] < 0 < balances[t.creditor] for t in result)
    #@ ensures all(balances[m] == sum(t.amount for t in result if t.creditor == m)
    #@                            - sum(t.amount for t in result if t.debtor == m)
    #@             for m in range(len(balances)))
    rest = balances[:]
    out: list[Transfer] = []
    n = len(rest)
    i = 0
    j = 0
    while i < n and j < n:
        #@ invariant len(rest) == n
        #@ invariant 0 <= i <= n and 0 <= j <= n
        #@ invariant sum(rest) == 0
        #@ invariant all(rest[k] >= 0 for k in range(i))
        #@ invariant all(rest[k] <= 0 for k in range(j))
        #@ invariant all(balances[k] <= rest[k] <= 0 or 0 <= rest[k] <= balances[k] for k in range(n))
        #@ invariant all(t.amount > 0 for t in out)
        #@ invariant all(0 <= t.debtor < n and 0 <= t.creditor < n for t in out)
        #@ invariant all(balances[t.debtor] < 0 < balances[t.creditor] for t in out)
        #@ invariant all(balances[m] - rest[m] == sum(t.amount for t in out if t.creditor == m)
        #@                                       - sum(t.amount for t in out if t.debtor == m)
        #@               for m in range(n))
        #@ decreases 2 * n - i - j
        if rest[i] >= 0:
            i += 1
        elif rest[j] <= 0:
            j += 1
        else:
            x = min(-rest[i], rest[j])
            out.append(Transfer(i, j, x))
            rest[i] = rest[i] + x
            rest[j] = rest[j] - x
            if rest[i] == 0:
                i += 1
            if rest[j] == 0:
                j += 1
    return out
