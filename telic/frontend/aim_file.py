"""`aims/<ID>.md`: one cross-file aim per file, next to the code it spans.

    aims/REFUND-CAP.md:
    WHEN a refund is requested, the shop shall refund at most what the
    customer paid, net of earlier refunds.
    by: refund_amount, web/checkout.ts::refundButton

The filename is the ID; the contents are one EARS sentence and an optional
``by:`` line. The directory containing ``aims/`` is the aim's scope.
"""

from __future__ import annotations

import os
import re
from pathlib import Path

from .. import ir
from ..contracts import AIM_ID
from ..aim import split_by

DIR = "aims"
LANGUAGE = "aims"

_ID = re.compile(rf"^{AIM_ID}$")


def is_aim_file(path: str) -> bool:
    """An entry directly in an aims/ directory other than its README and hidden
    files. Every such entry must be an <ID>.md file."""
    name = os.path.basename(os.path.normpath(path))
    return not name.startswith(".") and name.lower() != "readme.md" and os.path.basename(os.path.dirname(os.path.normpath(path))) == DIR


def aim_entry(path: str) -> str | None:
    """The aims/ entry a path is or lies inside, if any."""
    parts = os.path.normpath(path).split(os.sep)
    for i, part in enumerate(parts[:-1]):
        if part == DIR:
            entry = os.sep.join(parts[: i + 2])
            return entry if is_aim_file(entry) else None
    return None


def aim_files(directory: str) -> list[str]:
    """The entries of an aims/ directory, read through a symlink."""
    return sorted(p for p in (os.path.join(directory, f) for f in os.listdir(directory)) if is_aim_file(p))


def scope_of(path: str) -> str:
    """The directory an aim file governs, relative to the root ('' = all)."""
    return os.path.dirname(os.path.dirname(os.path.normpath(path))).replace(os.sep, "/")


def lower_aim_entry(path: str, full: str) -> ir.Module:
    """An aims/ entry at ``full``, reported as ``path``: an aim file, or a problem."""
    name = os.path.basename(path)
    if not name.endswith(".md") or not os.path.isfile(full):
        m = ir.Module(path=path, language=LANGUAGE, source="")
        kind = "directory" if os.path.isdir(full) else "file"
        m.problems.append((f"{DIR}/ holds only <ID>.md files and a README: rename or move the {kind} '{name}'", ir.Loc(1)))
        return m
    return lower_aim_file(path, Path(full).read_text())


def lower_aim_file(path: str, source: str) -> ir.Module:
    m = ir.Module(path=path, language=LANGUAGE, source=source)
    iid = os.path.basename(path)[: -len(".md")]
    if not _ID.match(iid):
        m.problems.append((f"'{os.path.basename(path)}' is not an aim ID: name the file <UPPER-KEBAB-ID>.md", ir.Loc(1)))
        return m
    lines = [(n, raw.strip()) for n, raw in enumerate(source.splitlines(), 1) if raw.strip()]
    for n, line in lines:
        if line.startswith("#"):
            m.problems.append((f"{iid}.md has a heading: the filename is the ID, so write only the sentence and an optional by: line", ir.Loc(n)))
            return m
    text = " ".join(" ".join(line for _, line in lines).split())
    if not split_by(text)[0]:
        m.problems.append((f"aim {iid} has no sentence: write one EARS sentence in {iid}.md", ir.Loc(1)))
        return m
    m.aims.append(ir.AimDecl(iid, text, ir.Loc(lines[0][0])))
    return m
