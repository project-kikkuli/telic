def overflowed_integer_prefix_disables_compensation() -> float:
    #@ ensures result == 1.0
    return sum([9223372036854775808, -9223372036854775808, 0.0, 1e16, 1, -1e16])


def out_of_range_item_disables_compensation() -> float:
    #@ ensures result == 1.0
    return sum([-1, 9223372036854775808, -9223372036854775807, 0.0, 1e16, 1, -1e16])
