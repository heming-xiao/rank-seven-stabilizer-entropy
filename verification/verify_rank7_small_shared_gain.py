"""Exact compact comparison with a bounded shared-anchor gain."""

from fractions import Fraction as F

from verify_rank7_equal_third_fourth import objectives, verify_unequal_outer
from verify_rank7_four_equal_tails import verify_cover


def main():
    absorption = F(1, 5)
    length_bound = 13
    verify_unequal_outer(length_bound, absorption)
    counts, outer, depth = verify_cover(
        (0, 1),
        objectives(length_bound, absorption, independent_middle_gap=True),
        ((0,), (1, 2)), 44, dimension=6,
        outer_faces=((0, 1, 5), (2, 3, 4)),
    )
    print(f"Shared-gain cone: {counts} comparison leaves, {outer} analytic leaves, depth {depth}.")


if __name__ == "__main__":
    main()

