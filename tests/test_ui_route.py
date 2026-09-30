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
