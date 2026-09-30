"""A machine-wide budget of browsers: telic UI runs in any number of
processes share ``TELIC_UI_SLOTS`` slots (default 2), one per browser, and
queue for them instead of stacking. A slot is a lock file held with
``flock``, so the operating system releases it when its holder exits, however
it exits."""

from __future__ import annotations

import fcntl
import os
import random
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Callable, Iterator

DEFAULT = 2


class SlotTimeout(Exception):
    pass


def total() -> int:
    try:
        return max(1, int(os.environ.get("TELIC_UI_SLOTS", DEFAULT)))
    except ValueError:
        return DEFAULT


def directory() -> Path:
    base = os.environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache")
    d = Path(base, "telic", "ui-slots")
    d.mkdir(parents=True, exist_ok=True)
    return d


def _try(n: int) -> list[int] | None:
    """``n`` free slots, all or none (holding some while waiting for more
    would deadlock two runs that each hold part of what they need)."""
    got: list[int] = []
    d = directory()
    for i in random.sample(range(total()), total()):
        fd = os.open(d / f"slot-{i}.lock", os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            os.close(fd)
            continue
        got.append(fd)
        if len(got) == n:
            return got
    for fd in got:
        os.close(fd)
    return None


@contextmanager
def hold(n: int = 1, timeout: float | None = None, log: Callable[[str], None] | None = None) -> Iterator[int]:
    """Hold ``n`` browser slots (at most the machine's total) until the block
    ends; yields how many."""
    n = max(1, min(n, total()))
    deadline = None if timeout is None else time.monotonic() + timeout
    waited = False
    while True:
        fds = _try(n)
        if fds is not None:
            break
        if deadline is not None and time.monotonic() > deadline:
            raise SlotTimeout(f"no {n} of the {total()} browser slots came free in {timeout:.0f}s")
        if not waited and log is not None:
            log(f"waiting for {n} of the {total()} browser slots other telic runs hold (TELIC_UI_SLOTS)")
        waited = True
        time.sleep(0.2 + random.random() * 0.3)
    try:
        yield n
    finally:
        for fd in fds:
            os.close(fd)
