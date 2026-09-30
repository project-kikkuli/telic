"""What telic needs from a platform to observe and drive an app.

An adapter for a new platform (iOS via XCUITest, Android via UIAutomator, a
desktop accessibility API) implements this and nothing else: learning and
checking only see ``Snapshot``s and ``Action``s.
"""

from __future__ import annotations

from .tree import Action, Node, Snapshot


class DriverError(Exception):
    """The user could not do it. ``moved``: the app may have changed anyway."""

    def __init__(self, msg: str, moved: bool = False):
        super().__init__(msg)
        self.moved = moved


class Driver:
    name = "driver"

    def start(self) -> None:
        """Launch whatever the adapter needs (a browser, a simulator)."""

    def stop(self) -> None:
        """Release it."""

    def reset(self) -> None:
        """A fresh app: no stored data, the start screen."""
        raise NotImplementedError

    def reopen(self) -> None:
        """Close and reopen the app, keeping what it stored."""
        raise NotImplementedError

    def observe(self) -> Snapshot:
        """The accessibility tree now, once the UI has settled."""
        raise NotImplementedError

    def do(self, action: Action) -> None:
        """Perform one action from the latest snapshot; raise DriverError if the user could not."""
        raise NotImplementedError

    def viewport(self, width: int, height: int) -> None:
        """Window or screen size for everything that follows."""
        raise NotImplementedError

    def uncovered(self, node: Node) -> tuple[bool, list[tuple[str, str | None]]]:
        """Hit-test an element from the latest snapshot at its center and
        corners: (operable, [(point, what covers it or None)]). An element
        with no size, or behind a modal dialog it is not part of, is not
        operable, so nothing can cover it."""
        raise NotImplementedError

    def leaves(self, node: Node) -> bool:
        """Would activating this element leave the app (an external link)?"""
        return False
