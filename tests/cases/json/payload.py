# An order API: the request body is validated once, then handled as data.
from typing import Any


#@ trusted
#@ ensures result == (isinstance(item, dict) and "sku" in item and isinstance(item["sku"], str)
#@     and "qty" in item and isinstance(item["qty"], int) and item["qty"] > 0)
def valid_item(item: Any) -> bool:
    return isinstance(item, dict) and isinstance(item.get("sku"), str) and isinstance(item.get("qty"), int) and item["qty"] > 0


#@ trusted
#@ ensures result == (isinstance(body, dict) and "customer" in body and isinstance(body["customer"], str)
#@     and "items" in body and isinstance(body["items"], list) and len(body["items"]) > 0
#@     and all(valid_item(i) for i in body["items"]))
def valid_order(body: Any) -> bool:
    return (
        isinstance(body, dict)
        and isinstance(body.get("customer"), str)
        and isinstance(body.get("items"), list)
        and len(body["items"]) > 0
        and all(valid_item(i) for i in body["items"])
    )


#@ aim ORDER-QTY: WHEN a valid order is received, the shop shall count at least one unit per line.
#@   by: total_quantity
#@ requires valid_order(body)
#@ [ORDER-QTY] ensures result >= len(body["items"])
def total_quantity(body: dict[str, Any]) -> int:
    items: list[Any] = body["items"]
    total = 0
    for k in range(len(items)):
        #@ invariant total >= k
        qty: int = items[k]["qty"]
        total += qty
    return total


#@ requires valid_order(body)
def customer(body: dict[str, Any]) -> str:
    name: str = body["customer"]
    return name


#@ requires valid_order(body)
def first_sku(body: dict[str, Any]) -> str:
    items: list[Any] = body["items"]
    sku: str = items[0]["sku"]
    return sku


#@ requires valid_order(body)
def missing_field(body: dict[str, Any]) -> Any:
    return body["shipping"]


#@ requires valid_order(body)
#@ ensures result >= 2
def overclaims(body: dict[str, Any]) -> int:
    items: list[Any] = body["items"]
    qty: int = items[0]["qty"]
    return qty


#@ ensures result
def unvalidated(body: dict[str, Any]) -> bool:
    return valid_order(body)
