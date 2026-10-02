"""Classify what a discharged function proof depends on."""

from __future__ import annotations

from typing import Any


def model_assumptions(function: Any) -> list[str]:
    return [
        text
        for _, text in function.assumptions
        if text.startswith("assumed: ") and not text.startswith("assumed: trusted predicate ")
    ]


def evidence_status(function: Any) -> str:
    if function.status != "proved":
        return function.status
    if function.open_deps or function.context_deps or model_assumptions(function):
        return "open"
    if function.trusted_deps or function.assumptions:
        return "trusted"
    return "proved"
