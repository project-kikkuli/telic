"""Machine-wide budgets shared by every telic process: browsers for UI runs
(``TELIC_UI_SLOTS``) and solver workers (``TELIC_MAX_JOBS``). A slot is a
lock file held with ``flock``, so the operating system releases it when its
holder exits, however it exits; runs queue for slots instead of stacking."""

from __future__ import annotations

import fcntl
import os
import random
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Callable, Iterator


class SlotTimeout(Exception):
    pass


class Slots:
    def __init__(self, name: str, env: str, default: Callable[[], int], what: str):
        self.name, self.env, self.default, self.what = name, env, default, what

    def total(self) -> int:
        try:
            return max(1, int(os.environ.get(self.env) or self.default()))
        except ValueError:
            return max(1, self.default())

    def directory(self) -> Path:
        # TELIC_SLOTS_DIR isolates a budget without moving everything else that lives in XDG_CACHE_HOME (browsers)
        base = os.environ.get("TELIC_SLOTS_DIR") or os.path.join(os.environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache"), "telic")
        d = Path(base, self.name)
        d.mkdir(parents=True, exist_ok=True)
        return d

    def _try(self, n: int, least: int) -> list[int] | None:
        """Up to ``n`` free slots, or none if fewer than ``least`` are free
        (holding some while waiting for more would deadlock two runs that
        each hold part of what they need)."""
        got: list[int] = []
        d, total = self.directory(), self.total()
        for i in random.sample(range(total), total):
            fd = os.open(d / f"slot-{i}.lock", os.O_RDWR | os.O_CREAT, 0o644)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError:
                os.close(fd)
                continue
            got.append(fd)
            if len(got) == n:
                return got
        if len(got) >= least:
            return got
        for fd in got:
            os.close(fd)
        return None

    @contextmanager
    def hold(self, n: int = 1, timeout: float | None = None, log: Callable[[str], None] | None = None, least: int | None = None) -> Iterator[int]:
        """Hold ``n`` slots (at most the machine's total) until the block
        ends, or with ``least``, whatever is free between ``least`` and
        ``n``; yields how many."""
        n = max(1, min(n, self.total()))
        least = n if least is None else max(1, min(least, n))
        deadline = None if timeout is None else time.monotonic() + timeout
        waited = False
        while True:
            fds = self._try(n, least)
            if fds is not None:
                break
            if deadline is not None and time.monotonic() > deadline:
                raise SlotTimeout(f"no {least} of the {self.total()} {self.what} slots came free in {timeout:.0f}s")
            if not waited and log is not None:
                log(f"waiting for {least} of the {self.total()} {self.what} slots other telic runs hold ({self.env})")
            waited = True
            time.sleep(0.2 + random.random() * 0.3)
        try:
            yield len(fds)
        finally:
            for fd in fds:
                os.close(fd)
