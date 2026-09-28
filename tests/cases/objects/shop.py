"""A typical vibecoded backend module."""
import logging
from datetime import datetime
from enum import Enum
from typing import Any, Optional

from pydantic import BaseModel

logger = logging.getLogger(__name__)
TAX_RATE = 8
MAX_ITEMS = 50


class Status(Enum):
    DRAFT = "draft"
    PAID = "paid"
    SHIPPED = "shipped"


class OutOfStock(Exception):
    pass


class Item(BaseModel):
    sku: str
    price_cents: int
    qty: int


class Order:
    #@ invariant self.total_cents >= 0

    def __init__(self, customer: str):
        self.customer = customer
        self.items: list[Item] = []
        self.status: Status = Status.DRAFT
        self.total_cents: int = 0
        self.created = datetime.now()

    def add(self, item: Item) -> None:
        #@ requires item.price_cents >= 0 and item.qty > 0
        #@ ensures self.total_cents >= old(self.total_cents)
        if len(self.items) >= MAX_ITEMS:
            raise OutOfStock(f"too many items for {self.customer}")
        self.items.append(item)
        self.total_cents += item.price_cents * item.qty
        logger.info(f"added {item.sku} x{item.qty}")

    def pay(self, payment_ref: str) -> None:
        #@ requires self.status == Status.DRAFT
        #@ ensures self.status == Status.PAID
        self.status = Status.PAID
        self.ref = payment_ref

    def label(self) -> str:
        return f"{self.customer.upper()}: {self.status.value} ({len(self.items)} items)"


def with_tax(cents: int) -> int:
    #@ requires cents >= 0
    #@ ensures result >= cents
    return cents + cents * TAX_RATE // 100


def discount(total: int, code: Optional[str], codes: dict[str, int]) -> int:
    #@ requires total >= 0
    #@ ensures 0 <= result <= total
    if code is None or code not in codes:
        return total
    pct = codes[code]
    return total - total * pct // 100


def parse_qty(raw: Any) -> int:
    #@ ensures result >= 1
    try:
        q = int(raw)
    except ValueError:
        return 1
    return max(q, 1)


async def checkout(order: Order, gateway: Any) -> bool:
    #@ requires order.status == Status.DRAFT
    ok = await gateway.charge(order.customer, with_tax(order.total_cents))
    if ok:
        order.pay("ref")
        return True
    return False


def summarize(orders: list[Order]) -> dict[str, int]:
    out: dict[str, int] = {}
    for o in orders:
        out[o.customer] = out.get(o.customer, 0) + o.total_cents
    return out


def skus(order: Order) -> list[str]:
    #@ ensures len(result) == len(order.items)
    return [i.sku for i in order.items]
