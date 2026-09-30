"""How many solver workers a run uses. A run asks for ``--jobs`` /
``TELIC_JOBS`` workers (default min(4, cores // 2)) and gets what is free of
the machine-wide ``TELIC_MAX_JOBS`` slots (default cores // 2), at least one;
with none free it waits. Worker processes, native-engine domains, replay
subprocesses and Lean checks all count."""

from __future__ import annotations

import os
import sys
import threading
import time
from contextlib import contextmanager
from typing import Iterator

from .slots import Slots


def _half() -> int:
    return max(1, (os.cpu_count() or 2) // 2)


BUDGET = Slots("job-slots", "TELIC_MAX_JOBS", _half, "solver")


def requested(jobs: int | None = None) -> int:
    if jobs:
        return max(1, jobs)
    try:
        return max(1, int(os.environ["TELIC_JOBS"]))
    except (KeyError, ValueError):
        return min(4, _half())


def _log(msg: str) -> None:
    print(f"telic: {msg}", file=sys.stderr, flush=True)


@contextmanager
def take(jobs: int | None, items: int | None = None) -> Iterator[int]:
    """Worker slots for ``items`` independent tasks, held until the block
    ends; yields how many workers to run."""
    want = requested(jobs) if items is None else min(requested(jobs), items)
    with BUDGET.hold(max(1, want), log=_log, least=1) as n:
        yield n


def exit_with_parent() -> None:
    """Pool-worker initializer: a worker whose run was killed exits, rather
    than living on as an orphan holding the run's slots."""
    parent = os.getppid()

    def watch() -> None:
        while os.getppid() == parent:
            time.sleep(0.5)
        os._exit(1)

    threading.Thread(target=watch, daemon=True).start()
