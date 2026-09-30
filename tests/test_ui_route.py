"""A screen is its route with record ids folded away."""

import pytest

from telic.ui.tree import route


@pytest.mark.parametrize(
    "path,screen",
    [
        ("/notes/42", "/notes/:id"),
        ("/groups/g1790764571078", "/groups/:id"),
        ("/x/3f2a9c1be07d", "/x/:id"),
        ("/groups/trip", "/groups/trip"),
        ("/v2/api", "/v2/api"),
        ("/users/ab12", "/users/ab12"),
    ],
)
def test_route(path, screen):
    assert route(path) == screen


@pytest.mark.parametrize(
    "path,patterns,screen",
    [
        ("/groups/trip", ("/groups/:id",), "/groups/:id"),
        ("/groups/trip/expenses/e1", ("/groups/:id", "/groups/:id/expenses/:e"), "/groups/:id/expenses/:e"),
        ("/groups/trip/settle", ("/groups/:id/*",), "/groups/:id/*"),
        ("/groups", ("/groups/:id",), "/groups"),
        ("/groups/", ("/groups/:id",), "/groups/"),
        ("/notes/42", ("/groups/:id",), "/notes/:id"),
    ],
)
def test_declared_route_names_the_screen(path, patterns, screen):
    from telic.ui.run import route_patterns

    class Lem:
        prop = None

    assert route(path, tuple(route_patterns(list(patterns), [Lem()]))) == screen


def test_a_lemma_screen_pattern_matches_any_segment():
    from telic.ui.spec import Pred
    from telic.ui.tree import Snapshot, Node

    p = Pred("screen", ("/groups/:id",))
    for screen, want in (("/groups/trip", True), ("/groups/:id", True), ("/groups", False), ("/groups/a/b", False)):
        assert p.eval(Snapshot(screen, Node("document")), "/") is want
