"""Tagged Python numeric values at dynamically typed boundaries."""

from __future__ import annotations

from dataclasses import dataclass

from . import logic as L


@dataclass(frozen=True)
class PyNumber:
    """An integer or binary64 value whose runtime kind is symbolic."""

    is_int: L.Term
    integer: L.Term
    floating: L.Term

    def as_float(self) -> L.Term:
        return L.ite(self.is_int, L.to_float(self.integer, L.FLOAT64), self.floating)

    def choose(self, condition: L.Term, other: PyNumber) -> PyNumber:
        return PyNumber(*(L.ite(condition, a, b) for a, b in zip(self.parts(), other.parts())))

    def parts(self) -> tuple[L.Term, L.Term, L.Term]:
        return self.is_int, self.integer, self.floating
