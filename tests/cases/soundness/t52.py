def mixed_sum_from_scalar_snapshot_is_not_nan() -> float:
    #@ ensures result != result
    x = 10**400
    xs = [x, -x, 0.0]
    return sum(xs)


def mixed_sum_after_slice_copy_is_not_nan() -> float:
    #@ ensures result != result
    x = 10**400
    xs = [x, -x, 0.0]
    ys = xs[:]
    return sum(ys)


def mixed_sum_after_copy_method_is_not_nan() -> float:
    #@ ensures result != result
    x = 10**400
    xs = [x, -x, 0.0]
    ys = xs.copy()
    return sum(ys)
