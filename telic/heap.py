"""Versioned symbolic heap layout shared with ``core/``."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from . import logic as L


ABI_VERSION = 1
LANGUAGE_TAGS = {"python": 1, "typescript": 2, "rust": 3, "swift": 4}
VALUE_TAGS = {
    "none": 0,
    "integer": 1,
    "real": 2,
    "boolean": 3,
    "text": 4,
    "reference": 5,
    "opaque": 6,
    "python_number": 7,
}
CELL_TAGS = {"free": 0, "list": 1, "dict": 2, "record": 3, "class": 4}


@dataclass(frozen=True)
class Layout:
    class_tags: tuple[tuple[str, int], ...]
    field_slots: tuple[tuple[str, str, int], ...]

    def json(self) -> dict[str, Any]:
        return {
            "version": ABI_VERSION,
            "language_tags": LANGUAGE_TAGS,
            "value_tags": VALUE_TAGS,
            "cell_tags": CELL_TAGS,
            "class_tags": [[name, tag] for name, tag in self.class_tags],
            "field_slots": [[owner, name, slot] for owner, name, slot in self.field_slots],
            "records": {
                "number": ["PythonNumber", [["is_int", "Bool"], ["integer", "Int"], ["floating", "Float64"]]],
                "box": "TelicValueV1",
                "key": "TelicKeyV1",
                "cell": "TelicCellV1",
            },
        }


def layout(program) -> Layout:
    names = sorted(program.classes)
    owners = sorted({
        (program.classes[c].field_owner(name), name)
        for c, decl in program.classes.items()
        for name, _ in decl.fields
    })
    return Layout(
        tuple((name, i + 1) for i, name in enumerate(names)),
        tuple((owner, name, i + 1) for i, (owner, name) in enumerate(owners)),
    )


def number_sort() -> L.Sort:
    """The numeric lane is the public numeric ABI, not a heap-local copy."""
    return L.REC("PythonNumber", (("is_int", L.BOOL), ("integer", L.INT), ("floating", L.FLOAT64)))

