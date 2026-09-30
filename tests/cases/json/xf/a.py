# One half of a shape defined across two files: even and odd call each other.
from typing import Any

from b import odd


#@ trusted
#@ ensures result == (isinstance(t, dict) and "n" in t and odd(t["n"]))
def even(t: Any) -> bool:
    return isinstance(t, dict) and "n" in t and odd(t["n"])
