def share_of(amount: int, parts: int, index: int) -> int:
    #@ requires amount >= 0
    #@ requires parts >= 1
    #@ requires 0 <= index < parts
    #@ ensures result >= 0
    if index < amount % parts:
        return amount // parts + 1
    return amount // parts


def split_equal(amount: int, parts: int) -> list[int]:
    #@ aim SPLIT-EXACT
    #@ requires amount >= 0
    #@ requires parts >= 1
    #@ ensures len(result) == parts
    #@ ensures sum(result) == amount
    #@ ensures all(s >= 0 for s in result)
    #@ ensures all(result[i] == share_of(amount, parts, i) for i in range(parts))
    base = amount // parts
    extra = amount % parts
    shares: list[int] = []
    for i in range(parts):
        #@ invariant len(shares) == i
        #@ invariant sum(shares) == base * i + min(i, extra)
        #@ invariant all(base <= s <= base + 1 for s in shares)
        #@ invariant all(shares[k] == share_of(amount, parts, k) for k in range(i))
        if i < extra:
            shares.append(base + 1)
        else:
            shares.append(base)
    return shares


def split_exact(amount: int, shares: list[int]) -> list[int]:
    #@ aim SPLIT-EXACT
    #@ requires amount >= 0
    #@ raises sum(shares) != amount or any(s < 0 for s in shares)
    #@ ensures sum(result) == amount
    #@ ensures all(s >= 0 for s in result)
    #@ ensures result == shares
    if any(s < 0 for s in shares):
        raise ValueError("a share is negative")
    if sum(shares) != amount:
        raise ValueError("shares do not add up to the amount")
    return shares[:]
