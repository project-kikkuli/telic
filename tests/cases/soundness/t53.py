def first_float_transition_is_ordinary() -> float:
    #@ ensures result == 2.0
    return sum([1, 1e16, 1, -1e16])
