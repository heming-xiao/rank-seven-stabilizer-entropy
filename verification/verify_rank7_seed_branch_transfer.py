"""Exact comparisons for transporting a highest-cut weighted seed."""

from fractions import Fraction as F


def check():
    rate = F(343, 10)
    radical_upper = 4-rate/64
    assert radical_upper > 0 and radical_upper**2 < 12
    assert 168*(1-F(5, 28)-F(1, 2)) == 54
    assert 168*(1-F(3, 14)-F(1, 2)) == 48
    assert 54*F(2, 3) > rate and 252*F(2, 3)**2 > 2*rate
    minimum_c = F(4, 3)*32/rate
    maximum_b = rate/24
    assert minimum_c == F(1280, 1029) and maximum_b == F(343, 240)
    discount = 1-(F(4, 3)-1)*(minimum_c-1)
    assert discount == F(2836, 3087)
    largest_x = F(2700, 61)*discount
    leftover = 252*F(2, 3)**2+84*F(2, 3)**2-rate*maximum_b
    assert (rate-32)*largest_x < leftover
    assert F(1800, 61)*F(122, 25) == 144
    print("Weighted seed transfer constants checked exactly.")


if __name__ == "__main__":
    check()

