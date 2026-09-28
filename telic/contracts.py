"""Language-neutral parsing of ``@`` contract comments.

A contract comment is a line comment whose body starts with ``@``::

    #@ requires 0 <= refunded <= paid          (Python)
    //@ ensures result >= 0                    (TypeScript)

This module only splits comment text into keyword + payload; each frontend
parses the payload as an expression in its own host language, which is what
keeps contracts legible (they are just code) and runtime-checkable.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

CLAUSE_KEYWORDS = {
    "requires",
    "ensures",
    "invariant",
    "decreases",
    "assert",
    "assume",
    "raises",
}
DIRECTIVE_KEYWORDS = {"intent", "index", "mirrors", "trusted", "pure"}
KEYWORDS = CLAUSE_KEYWORDS | DIRECTIVE_KEYWORDS

FUNCTION_KEYWORDS = {"requires", "ensures", "decreases", "raises", "intent", "mirrors", "trusted", "pure"}
LOOP_KEYWORDS = {"invariant", "decreases", "index"}
STATEMENT_KEYWORDS = {"assert", "assume"}

INTENT_ID = r"[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*"
_TAG = re.compile(rf"^\[\s*({INTENT_ID}(?:\s*,\s*{INTENT_ID})*)\s*\]\s*")
_INTENT_DECL = re.compile(rf"^({INTENT_ID})\s*(?::\s*(.*))?$")
_INTENT_LIST = re.compile(rf"^{INTENT_ID}(?:\s*,\s*{INTENT_ID})*$")


@dataclass
class ContractLine:
    """One logical contract line (continuations already joined)."""

    keyword: str
    payload: str
    line: int  # line of the keyword
    col: int  # column of the comment marker
    payload_col: int  # column where the payload starts (first physical line)
    tags: tuple[str, ...] = ()
    end_line: int = 0
    consumed: bool = False
    raw_lines: list[int] = field(default_factory=list)


class ContractSyntaxError(Exception):
    def __init__(self, msg: str, line: int, col: int = 0):
        super().__init__(msg)
        self.line = line
        self.col = col


def parse_comment_lines(comments: list[tuple[int, int, str]], marker: str) -> list[ContractLine]:
    """Turn raw ``(line, col, text)`` comments into contract lines.

    ``text`` is the full comment including its marker (``#`` or ``//``).
    Lines whose first word is not a keyword continue the previous contract
    line, which lets long clauses wrap::

        #@ ensures all(result[i] <= result[i + 1]
        #@             for i in range(len(result) - 1))
    """
    out: list[ContractLine] = []
    prefix = marker + "@"
    for line, col, text in comments:
        if not text.startswith(prefix):
            continue
        body = text[len(prefix):]
        stripped = body.strip()
        lead = len(body) - len(body.lstrip())
        base_col = col + len(prefix) + lead
        if not stripped:
            continue
        tags: tuple[str, ...] = ()
        m = _TAG.match(stripped)
        if m:
            tags = tuple(t.strip() for t in m.group(1).split(","))
            base_col += m.end()
            stripped = stripped[m.end():]
        word = stripped.split(None, 1)[0] if stripped else ""
        if word in KEYWORDS:
            payload = stripped[len(word):]
            pl = len(payload) - len(payload.lstrip())
            out.append(
                ContractLine(
                    keyword=word,
                    payload=payload.strip(),
                    line=line,
                    col=col,
                    payload_col=base_col + len(word) + pl,
                    tags=tags,
                    end_line=line,
                    raw_lines=[line],
                )
            )
        elif out and out[-1].end_line == line - 1 and not tags:
            prev = out[-1]
            prev.payload = prev.payload + "\n" + stripped
            prev.end_line = line
            prev.raw_lines.append(line)
        else:
            raise ContractSyntaxError(
                f"unknown contract keyword '{word}' (expected one of: {', '.join(sorted(KEYWORDS))})",
                line,
                col,
            )
    return out


def parse_intent_directive(cl: ContractLine) -> tuple[list[str], str | None]:
    """``intent ID: sentence`` declares; ``intent A, B`` links."""
    payload = " ".join(cl.payload.split())
    m = _INTENT_DECL.match(payload)
    if m and m.group(2) is not None:
        return [m.group(1)], m.group(2).strip()
    if _INTENT_LIST.match(payload):
        return [p.strip() for p in payload.split(",")], None
    raise ContractSyntaxError(
        "malformed intent: write '@intent ID: sentence' to declare or '@intent ID' to link",
        cl.line,
        cl.col,
    )
