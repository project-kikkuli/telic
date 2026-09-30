"""The browser budget: every browser takes one of ``TELIC_UI_SLOTS`` slots
(default 2) shared by all telic runs on the machine."""

from __future__ import annotations

from ..slots import Slots, SlotTimeout

DEFAULT = 2

BROWSERS = Slots("ui-slots", "TELIC_UI_SLOTS", lambda: DEFAULT, "browser")
hold = BROWSERS.hold
total = BROWSERS.total
directory = BROWSERS.directory

__all__ = ["BROWSERS", "DEFAULT", "SlotTimeout", "directory", "hold", "total"]
