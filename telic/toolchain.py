"""Identities of the exact solver executables selected for a verification run."""

from __future__ import annotations

import hashlib
import os
import platform
import shutil
import subprocess
from pathlib import Path


def _executable(path: str | None, args: tuple[str, ...]) -> tuple[str, str] | None:
    if not path:
        return None
    candidate = Path(path)
    found = str(candidate.resolve()) if candidate.is_file() else shutil.which(path)
    if not found or not os.path.isfile(found):
        return ("unavailable", "")
    binary = Path(found).resolve()
    try:
        result = subprocess.run([str(binary), *args], capture_output=True, text=True, timeout=10)
        version = (result.stdout or result.stderr).strip()
    except (OSError, subprocess.TimeoutExpired) as exc:
        version = f"unavailable:{type(exc).__name__}"
    return (version, hashlib.sha256(binary.read_bytes()).hexdigest())


def python_z3() -> tuple[str, str] | None:
    import z3
    import z3.z3core as z3core

    lib_dir = Path(z3core._z3_lib_resource_path)
    suffix = {"Darwin": ".dylib", "Windows": ".dll"}.get(platform.system(), ".so")
    candidates = sorted(lib_dir.glob(f"*z3*{suffix}"))
    if not candidates:
        return (z3.get_version_string(), "")
    lib = next((p for p in candidates if p.name == f"libz3{suffix}"), candidates[0])
    return (z3.get_version_string(), hashlib.sha256(lib.read_bytes()).hexdigest())


def native_z3() -> tuple[str, str, str] | None:
    return _executable(os.environ.get("TELIC_Z3") or "z3", ("--version",))


def lean() -> tuple[str, str, str] | None:
    from .lean import find_lean

    return _executable(find_lean(), ("--version",))


def core() -> tuple[str, str, str] | None:
    from .engine import CORE_DIR

    override = os.environ.get("TELIC_CORE")
    local = CORE_DIR / "telic-core"
    path = override if override and os.path.exists(override) else str(local) if local.exists() else shutil.which("telic-core")
    return _executable(path, ("--source-hash",))
