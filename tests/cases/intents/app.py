#@ intent CAP: WHEN a refund is requested, the shop shall refund at most what was paid.
#@   by: refund, audit
#@ intent LOOSE: refunds are small and also fast. They never fail.
#@ intent LONELY: The shop shall log every refund.


def refund(paid: int, requested: int) -> int:
    #@ requires paid >= 0 and requested >= 0
    #@ intent CAP
    #@ ensures result <= paid
    return min(paid, requested)


def audit(x: int) -> int:
    return x


def stray(paid: int) -> int:
    #@ requires paid >= 0
    #@ [CAP] ensures result >= 0
    #@ [LOOSE] ensures result <= paid
    return paid


def ghost(x: int) -> int:
    #@ [UNDECLARED-ONE] ensures result == x
    return x
