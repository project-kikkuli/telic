# A trusted predicate whose @ensures cannot hold is vacuous, and so is every
# proof that assumes it, directly or through a cycle of predicates.
from typing import Any


#@ trusted
#@ ensures result == (not liar(t))
def liar(t: Any) -> bool:
    return False


#@ requires liar(t)
#@ ensures result == 1
def use_liar(t: Any) -> int:
    return 2


#@ trusted
#@ ensures result == (not q(t))
def p(t: Any) -> bool:
    return True


#@ trusted
#@ ensures result == p(t)
def q(t: Any) -> bool:
    return True
