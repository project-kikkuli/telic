import os
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent

RUN = """
import sys, time
from telic.checker import run_parallel

def work(i):
    t = time.time()
    time.sleep(0.3)
    with open(sys.argv[1], "a") as f:
        f.write(f"{t} {time.time()}\\n")
    return i

n = int(sys.argv[2])
print("start", flush=True)
assert run_parallel(work, list(range(n)), int(sys.argv[3])) == list(range(n))
"""


def _env(tmp_path, budget: int) -> dict[str, str]:
    env = {k: v for k, v in os.environ.items() if k not in ("TELIC_JOBS", "TELIC_MAX_JOBS")}
    return {**env, "PYTHONPATH": str(ROOT), "XDG_CACHE_HOME": str(tmp_path), "TELIC_MAX_JOBS": str(budget)}


def _peak(lines: list[str]) -> int:
    events = sorted(ev for ln in lines for ev in ((float(ln.split()[0]), 1), (float(ln.split()[1]), -1)))
    peak = cur = 0
    for _, d in events:
        cur += d
        peak = max(peak, cur)
    return peak


@pytest.mark.parametrize("budget", [2, 3])
def test_concurrent_runs_never_exceed_the_machine_job_budget(tmp_path, budget):
    log = tmp_path / "work.log"
    runs = [subprocess.Popen([sys.executable, "-c", RUN, str(log), "12", str(budget)], env=_env(tmp_path, budget), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) for _ in range(2)]
    for r in runs:
        _, err = r.communicate(timeout=120)
        assert r.returncode == 0, err
    lines = log.read_text().splitlines()
    assert len(lines) == 24
    assert _peak(lines) <= budget


def test_a_killed_run_frees_its_job_slots(tmp_path, monkeypatch):
    from telic import jobs
    from telic.slots import SlotTimeout

    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path))
    monkeypatch.setenv("TELIC_MAX_JOBS", "2")
    run = subprocess.Popen([sys.executable, "-c", RUN, str(tmp_path / "work.log"), "100", "2"], env=_env(tmp_path, 2), stdout=subprocess.PIPE, text=True)
    try:
        assert run.stdout.readline().strip() == "start"
        deadline = time.monotonic() + 30
        while not (tmp_path / "work.log").exists() and time.monotonic() < deadline:
            time.sleep(0.1)
        with pytest.raises(SlotTimeout):
            with jobs.BUDGET.hold(1, timeout=0.5):
                pass
        run.send_signal(signal.SIGKILL)
        run.wait(timeout=10)
        with jobs.BUDGET.hold(2, timeout=10) as n:
            assert n == 2
    finally:
        run.kill()


def test_a_run_takes_what_is_free_and_waits_for_at_least_one(tmp_path, monkeypatch):
    from telic import jobs
    from telic.slots import SlotTimeout

    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path))
    monkeypatch.setenv("TELIC_MAX_JOBS", "3")
    with jobs.BUDGET.hold(2):
        with jobs.take(4, 100) as n:
            assert n == 1
        with jobs.BUDGET.hold(1), pytest.raises(SlotTimeout):
            with jobs.BUDGET.hold(4, timeout=0.5, least=1):
                pass


@pytest.mark.parametrize(
    "cores, env, flag, want",
    [(12, None, None, 4), (4, None, None, 2), (1, None, None, 1), (12, "8", None, 8), (12, "8", 3, 3), (12, "junk", None, 4)],
)
def test_jobs_per_run(monkeypatch, cores, env, flag, want):
    from telic import jobs

    monkeypatch.setattr(os, "cpu_count", lambda: cores)
    if env is None:
        monkeypatch.delenv("TELIC_JOBS", raising=False)
    else:
        monkeypatch.setenv("TELIC_JOBS", env)
    assert jobs.requested(flag) == want
