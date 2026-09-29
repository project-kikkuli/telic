from .models import FEE_CENTS, Invoice, Status, fee
from . import models


#@ aim NO-OVERPAY: IF a payment exceeds what is owed THEN the system shall
#@   reject it without changing the invoice.
#@   by: settle, models.py::Invoice.pay


def settle(inv: Invoice, cents: int) -> bool:
    #@ aim NO-OVERPAY
    #@ ensures implies(not result, inv.paid == old(inv.paid))
    if cents <= 0 or cents > inv.amount - inv.paid:
        return False
    inv.pay(cents)
    return True


def total_with_fee(amount: int) -> int:
    #@ requires amount >= 0
    #@ ensures result >= amount + FEE_CENTS
    return amount + fee(amount)


def bad_total(amount: int) -> int:
    #@ requires amount >= 0
    #@ ensures result >= amount + 2 * FEE_CENTS
    return amount + models.fee(amount)


def open_invoice(amount: int) -> Invoice:
    #@ requires amount >= 0
    #@ ensures result.status == Status.OPEN
    return Invoice(amount)
