import os
import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from telic.checker import CheckOptions, check  # noqa: E402
from telic.lean import find_lean  # noqa: E402

HAS_NODE = shutil.which("node") is not None
HAS_LEAN = find_lean() is not None

needs_node = pytest.mark.skipif(not HAS_NODE, reason="Node.js not available")
needs_lean = pytest.mark.skipif(not HAS_LEAN, reason="Lean 4 not available")


def run_check(tmp_path, files: dict[str, str], **kw):
    """Write files into tmp_path and check them; returns the Report."""
    for name, text in files.items():
        p = tmp_path / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    opts = CheckOptions(cache_path=None, **kw)
    return check([str(tmp_path / n) for n in files], opts, root=str(tmp_path))


def statuses(report):
    return {f.fn.name: f.status for f in report.functions}


@pytest.fixture
def checker(tmp_path):
    def go(files, **kw):
        return run_check(tmp_path, files, **kw)

    return go


@pytest.fixture(autouse=True)
def _offline_generative_oracles(monkeypatch):
    """Writing mutants and proposing contracts default to `claude -p` when it
    is installed; tests use the builtin rules unless they pass an oracle."""
    for task in ("MUTATE", "STRENGTHEN"):
        monkeypatch.setenv(f"TELIC_ORACLE_{task}", "builtin")
