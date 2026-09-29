"""`intents/<ID>.md`: one cross-file intent per file, next to the code it spans.

    intents/REFUND-CAP.md:
    WHEN a refund is requested, the shop shall refund at most what the
    customer paid, net of earlier refunds.
    by: refund_amount, web/checkout.ts::refundButton

The filename is the ID; the contents are one EARS sentence and an optional
``by:`` line. The directory containing ``intents/`` is the intent's scope.
"""

from __future__ import annotations

import os
import re

from .. import ir
from ..contracts import INTENT_ID
from ..intent import split_by

DIR = "intents"
LANGUAGE = "intents"

_ID = re.compile(rf"^{INTENT_ID}$")


def is_intent_file(path: str) -> bool:
    return path.endswith(".md") and os.path.basename(os.path.dirname(os.path.normpath(path))) == DIR


def scope_of(path: str) -> str:
    """The directory an intent file governs, relative to the root ('' = all)."""
    return os.path.dirname(os.path.dirname(os.path.normpath(path))).replace(os.sep, "/")


def lower_intent_file(path: str, source: str) -> ir.Module:
    m = ir.Module(path=path, language=LANGUAGE, source=source)
    iid = os.path.basename(path)[: -len(".md")]
    if not _ID.match(iid):
        m.problems.append((f"'{os.path.basename(path)}' is not an intent ID: name the file <UPPER-KEBAB-ID>.md", ir.Loc(1)))
        return m
    lines = [(n, raw.strip()) for n, raw in enumerate(source.splitlines(), 1) if raw.strip()]
    for n, line in lines:
        if line.startswith("#"):
            m.problems.append((f"{iid}.md has a heading: the filename is the ID, so write only the sentence and an optional by: line", ir.Loc(n)))
            return m
    text = " ".join(" ".join(line for _, line in lines).split())
    if not split_by(text)[0]:
        m.problems.append((f"intent {iid} has no sentence: write one EARS sentence in {iid}.md", ir.Loc(1)))
        return m
    m.intents.append(ir.IntentDecl(iid, text, ir.Loc(lines[0][0])))
    return m
