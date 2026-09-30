"""The iOS adapter: the accessibility tree as AXe reports it, the [ui]
config for an iOS app, and the fixture SwiftUI app in a real simulator."""

from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from fake_simulator import FakeSimulator

from telic.checker import CheckOptions, check
from telic.ui import sim
from telic.ui.config import ConfigError, load
from telic.ui.ios import parse_ax, screen_of
from telic.ui.tree import Snapshot, actions

HERE = Path(__file__).parent / "cases" / "ui"
APP = HERE / "ios-app"


@pytest.mark.parametrize(
    "body, says",
    [
        ('platform = "ios"\napp = "build/A.app"\n', None),
        (
            'platform = "ios"\nproject = "A.xcodeproj"\nscheme = "A"\ndevices = ["iPhone 17"]\n',
            None,
        ),
        ('platform = "ios"\n', "needs 'app'"),
        ('platform = "ios"\nproject = "A.xcodeproj"\n', "needs 'app'"),
        (
            'platform = "ios"\napp = "A.app"\nviewports = ["390x844"]\n',
            "list device types in 'devices'",
        ),
        ('platform = "android"\napp = "A.apk"\n', 'platform is "web"'),
    ],
)
def test_an_ios_config_says_what_it_needs(tmp_path, body, says):
    (tmp_path / "telic.toml").write_text("[ui]\n" + body)
    if says is None:
        cfg = load(str(tmp_path / "telic.toml"), str(tmp_path))
        assert cfg.platform == "ios"
        return
    with pytest.raises(ConfigError, match=says):
        load(str(tmp_path / "telic.toml"), str(tmp_path))


# ---------------------------------------------------------------------------
# The adapter against a fake simulator (tests/fake_simulator.py)

PLIST = b"""<?xml version="1.0" encoding="UTF-8"?>
<plist version="1.0"><dict><key>CFBundleIdentifier</key><string>dev.telic.fixture</string></dict></plist>
"""


@pytest.fixture
def fake(monkeypatch):
    f = FakeSimulator()
    monkeypatch.setattr(sim, "available", lambda: None)
    monkeypatch.setattr(sim, "device", lambda kind: "FAKE-UDID")
    monkeypatch.setattr(sim, "boot", lambda udid: True)
    monkeypatch.setattr(sim, "simctl", f.simctl)
    monkeypatch.setattr(sim, "axe", f.axe)
    return f


def fake_app(tmp_path, bugs=()):
    d = tmp_path / "app"
    d.mkdir()
    shutil.copy(APP / "App.swift", d / "App.swift")
    (d / "Fake.app").mkdir()
    (d / "Fake.app" / "Info.plist").write_bytes(PLIST)
    args = f"launch_args = {json.dumps(['-TelicBugs', ','.join(bugs)])}\n" if bugs else ""
    (d / "telic.toml").write_text(f'[ui]\nplatform = "ios"\napp = "Fake.app"\ndevices = ["iPhone 17"]\nsettle_ms = 1\n{args}')
    return d


def test_the_tree_gives_screens_overlays_states_and_actions(fake):
    fake.installed = True
    fake.simctl("launch", "FAKE-UDID", fake.bundle)
    fake.stack.append("Settings")
    fake.saved["dark"] = True
    root = parse_ax(fake.tree())
    snap = Snapshot(screen_of(root), root)
    (switch,) = [n for n in snap.nodes() if n.role == "switch"]
    assert (snap.screen, snap.overlays(), switch.name, "checked" in switch.states) == (
        "Settings",
        [],
        "Dark mode",
        True,
    )
    assert sorted(a.label for a in actions(snap)[0]) == [
        'click button "Home"',
        'click switch "Dark mode"',
    ]
    fake.stack.pop()
    fake.sheet = "Help"
    root = parse_ax(fake.tree())
    assert Snapshot(screen_of(root), root).overlays() == ['dialog "Help"']


def test_fake_fixture_keeps_every_promise(tmp_path, fake):
    rep, got = run_ui(fake_app(tmp_path))
    assert {k: r.status for k, r in got.items()} == {
        "escape": "proved",
        "dark-mode-shown": "proved",
        "dark-mode": "proved",
        "menu-visible": "proved",
    }
    (m,) = rep.ui.apps[0].models
    assert m["complete"] and m["states"] >= 5 and m["viewport"] == "iPhone 17"
    # a fresh start reinstalls; reopening only relaunches
    assert ("uninstall", "FAKE-UDID", fake.bundle) in fake.calls and (
        "install",
        "FAKE-UDID",
        str(tmp_path / "app" / "Fake.app"),
    ) in fake.calls


@pytest.mark.parametrize(
    "bug, lemma, says",
    [
        ("trap", "escape", 'stuck at screen Help with dialog "Help" open'),
        ("forget", "dark-mode", "reopened the app: unchecked"),
        ("banner", "menu-visible", 'covered by button "Accept"'),
    ],
)
def test_fake_fixture_bugs_are_found_and_replayed(tmp_path, fake, bug, lemma, says):
    _, got = run_ui(fake_app(tmp_path, [bug]))
    r = got[lemma]
    assert r.status == "refuted" and says in r.detail and r.trace is not None, r.detail
    assert r.replay is None or r.replay["confirmed"]
    assert {k for k, x in got.items() if x.status == "refuted"} == {lemma}


def test_leaving_the_app_is_blocked_not_followed(tmp_path, fake):
    run_ui(fake_app(tmp_path))
    model = json.loads((tmp_path / "app" / ".telic" / "ui-model-iPhone 17.json").read_text())
    blocked = [why for st in model["states"] for why in st.get("blocked", {}).values()]
    assert "leaves the app (to Safari)" in blocked


# ---------------------------------------------------------------------------
# The fixture app in the iOS Simulator

needs_simulator = pytest.mark.skipif(
    sim.available() is not None,
    reason=f"iOS Simulator not available: {sim.available()}",
)


def fixture_app(tmp_path, bugs=()):
    d = tmp_path / "app"
    shutil.copytree(APP, d, ignore=shutil.ignore_patterns("build", ".telic"))
    if bugs:
        with (d / "telic.toml").open("a") as fh:
            fh.write(f"launch_args = {json.dumps(['-TelicBugs', ','.join(bugs)])}\n")
    return d


def run_ui(d):
    rep = check([str(d)], CheckOptions(cache_path=None, lean=False), root=str(d))
    return rep, {r.lemma.name: r for r in rep.ui.results}


@needs_simulator
def test_fixture_app_keeps_every_promise(tmp_path):
    rep, got = run_ui(fixture_app(tmp_path))
    assert {k: r.status for k, r in got.items()} == {
        "escape": "proved",
        "dark-mode-shown": "proved",
        "dark-mode": "proved",
        "menu-visible": "proved",
    }
    (m,) = rep.ui.apps[0].models
    assert m["complete"] and m["states"] > 4


@pytest.mark.parametrize(
    "bug, lemma, says",
    [
        ("trap", "escape", "stuck at screen Help"),
        ("forget", "dark-mode", "reopened the app: unchecked"),
        ("banner", "menu-visible", 'covered by button "Accept"'),
    ],
)
@needs_simulator
def test_fixture_bugs_are_found_and_replayed(tmp_path, bug, lemma, says):
    _, got = run_ui(fixture_app(tmp_path, [bug]))
    r = got[lemma]
    assert r.status == "refuted" and says in r.detail and r.trace is not None
    assert r.replay is None or r.replay["confirmed"]
    assert {k for k, x in got.items() if x.status == "refuted"} == {lemma}
