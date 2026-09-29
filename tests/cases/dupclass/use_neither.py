# Box reaches this file only through make_a's signature.
from use_a import make_a


def via_signature() -> int:
    #@ ensures result >= 0
    return make_a().v
