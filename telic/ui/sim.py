"""The iOS Simulator from the command line: ``xcrun simctl`` for devices and
apps, AXe (``brew install cameroncooke/axe/axe``) for the accessibility tree
and touches."""

from __future__ import annotations

import json
import os
import plistlib
import re
import shutil
import subprocess

from .driver import DriverError

PREFIX = "telic "  # devices telic creates are named after their device type


def run(args: list[str], timeout: float = 60, check: bool = True) -> str:
    try:
        p = subprocess.run(args, capture_output=True, text=True, timeout=timeout, check=False)
    except FileNotFoundError:
        raise DriverError(f"{args[0]} is not installed") from None
    except subprocess.TimeoutExpired:
        raise DriverError(f"'{' '.join(args[:4])}' did not finish within {timeout:.0f}s", moved=True) from None
    if check and p.returncode != 0:
        why = (p.stderr or p.stdout).strip().splitlines()
        raise DriverError(
            f"'{' '.join(args[:4])}' failed: {why[-1] if why else f'exit {p.returncode}'}",
            moved=True,
        )
    return p.stdout


def simctl(*args: str, timeout: float = 120, check: bool = True) -> str:
    return run(["xcrun", "simctl", *args], timeout, check)


def axe_path() -> str | None:
    return shutil.which("axe")


def available() -> str | None:
    """Why the iOS driver cannot run here, or None when it can."""
    if shutil.which("xcrun") is None:
        return "xcrun is missing: install Xcode"
    p = subprocess.run(
        ["xcrun", "simctl", "list", "runtimes", "-j"],
        capture_output=True,
        text=True,
        check=False,
    )
    if p.returncode != 0:
        return "simctl is unavailable: install Xcode and select it with 'sudo xcode-select -s /Applications/Xcode.app'"
    if not _runtimes(json.loads(p.stdout)):
        return "no iOS simulator runtime: run 'xcodebuild -downloadPlatform iOS'"
    if axe_path() is None:
        return "AXe is missing: brew install cameroncooke/axe/axe"
    return None


def _runtimes(data: dict) -> list[dict]:
    rts = [r for r in data.get("runtimes", []) if r.get("platform", "iOS") == "iOS" and r.get("isAvailable") and "iOS" in r.get("name", "")]
    return sorted(rts, key=lambda r: [int(x) for x in re.findall(r"\d+", r.get("version", "0"))])


def default_device() -> str:
    """The newest runtime's plain iPhone (no Pro, Max, Plus, mini)."""
    rts = _runtimes(json.loads(simctl("list", "runtimes", "-j")))
    if not rts:
        raise DriverError("no iOS simulator runtime: run 'xcodebuild -downloadPlatform iOS'")
    names = [t["name"] for t in rts[-1].get("supportedDeviceTypes", []) if re.fullmatch(r"iPhone \d+", t.get("name", ""))]
    if not names:
        raise DriverError(f"{rts[-1]['name']} supports no plain iPhone: name one in [ui] devices")
    return max(names, key=lambda n: int(n.split()[1]))


def device(kind: str) -> str:
    """The UDID of telic's simulator of this device type on the newest
    runtime, created the first time."""
    rts = _runtimes(json.loads(simctl("list", "runtimes", "-j")))
    if not rts:
        raise DriverError("no iOS simulator runtime: run 'xcodebuild -downloadPlatform iOS'")
    rt = rts[-1]
    types = {t["name"]: t["identifier"] for t in rt.get("supportedDeviceTypes", [])}
    if kind not in types:
        near = sorted(n for n in types if n.split()[0] == kind.split()[0])
        raise DriverError(f"{rt['name']} has no device type {kind!r} (it has: {', '.join(near or sorted(types))})")
    devs = json.loads(simctl("list", "devices", "-j")).get("devices", {}).get(rt["identifier"], [])
    for d in devs:
        if d.get("name") == PREFIX + kind and d.get("isAvailable", True):
            return d["udid"]
    return simctl("create", PREFIX + kind, types[kind], rt["identifier"]).strip()


def booted() -> list[str]:
    data = json.loads(simctl("list", "devices", "booted", "-j"))
    return [d["udid"] for ds in data.get("devices", {}).values() for d in ds if d.get("state") == "Booted"]


def boot(udid: str) -> bool:
    """Boot it and wait until it is ready; True if this call booted it."""
    if udid in booted():
        return False
    simctl("boot", udid)
    simctl("bootstatus", udid, "-b", timeout=300)
    return True


def bundle_id(app: str) -> str:
    try:
        with open(os.path.join(app, "Info.plist"), "rb") as fh:
            return str(plistlib.load(fh)["CFBundleIdentifier"])
    except (OSError, KeyError, ValueError) as e:
        raise DriverError(f"{app} is not an app bundle: {e}") from None


def axe(*args: str, udid: str, timeout: float = 30) -> str:
    return run([axe_path() or "axe", *args, "--udid", udid], timeout)
