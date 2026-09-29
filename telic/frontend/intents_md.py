"""`intents.md`: cross-file intents, declared next to the code they span.

    ## REFUND-CAP
    WHEN a refund is requested, the shop shall refund at most what the
    customer paid, net of earlier refunds.
    by: refund_amount, web/checkout.ts::refundButton

Each ``## ID`` heading declares one intent; the lines under it, up to the next
heading, are its sentence and an optional ``by:`` line. Anything before the
first ``##`` is free prose. The file's directory is the intent's scope.
"""

from __future__ import annotations

import os
import re

from .. import ir
from ..contracts import INTENT_ID
from ..intent import split_by

NAME = "intents.md"
LANGUAGE = "intents"

_HEADING = re.compile(r"^(#{1,6})\s+(.*?)\s*#*\s*$")
_ID = re.compile(rf"^{INTENT_ID}$")


def is_intents_file(path: str) -> bool:
    return os.path.basename(path) == NAME


def scope_of(path: str) -> str:
    """The directory an intents.md governs, relative to the root ('' = all)."""
    return os.path.dirname(os.path.normpath(path)).replace(os.sep, "/")


def lower_intents_md(path: str, source: str) -> ir.Module:
    m = ir.Module(path=path, language=LANGUAGE, source=source)
    current: tuple[str, int] | None = None
    body: list[str] = []
    fence = False

    def close() -> None:
        if current is None:
            return
        iid, line = current
        text = " ".join(" ".join(body).split())
        if not split_by(text)[0]:
            m.problems.append((f"intent {iid} has no sentence: write one EARS sentence under its heading", ir.Loc(line)))
        else:
            m.intents.append(ir.IntentDecl(iid, text, ir.Loc(line)))

    for n, raw in enumerate(source.splitlines(), 1):
        line = raw.strip()
        if line.startswith(("```", "~~~")):
            fence = not fence
            continue
        h = None if fence else _HEADING.match(line)
        if h is None:
            if current is not None and not fence:
                body.append(line)
            continue
        close()
        current, body = None, []
        if len(h.group(1)) != 2:
            continue
        if _ID.match(h.group(2)):
            current = (h.group(2), n)
        else:
            m.problems.append((f"'## {h.group(2)}' is not an intent ID: headings name one UPPER-KEBAB id", ir.Loc(n)))
    close()
    return m
