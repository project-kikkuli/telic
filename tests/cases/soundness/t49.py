def compensated_mixed_sum_is_not_zero() -> float:
    #@ ensures result == 0.0
    return sum([1e16, 1, -1e16])
