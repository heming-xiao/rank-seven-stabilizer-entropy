"""Check the five-tail weighted loss and its split-transport algebra exactly."""
from fractions import Fraction as F
from itertools import combinations

from verify_rank7_low_head_tail_prices import (
    CAPS, HIGHEST, KNOWN_ROWS, REF, ROWS, SHARED, TOP, WEDGES, verify_dual,
)


def directed_prefix(i, j):
    left = range(2, 2 + i)
    right = range(2, 2 + j)
    return [sum(int({0, 1, x, y} <= wedge) for x in left for y in right if x != y)
            for wedge in WEDGES]


def check_dual(cost, ref, rows):
    prices = [[KNOWN_ROWS.index((kind, labels, cap)), str(price)]
              for kind, labels, cap, price in rows]
    assert verify_dual(prices, ROWS, CAPS, cost) == ref
    assert sum(x * f for x, f in zip(cost, REF)) == ref


def verify_prefixes():
    # The symmetric forward expansion uses gaps at prefix lengths 2,3,4,5.
    # Each off-diagonal prefix is counted twice before division by two.
    for s, t in combinations((2, 3, 4, 5), 2):
        assert directed_prefix(s, t) == directed_prefix(t, s)
    p22, p23 = directed_prefix(2, 2), directed_prefix(2, 3)
    p34, p44 = directed_prefix(3, 4), directed_prefix(4, 4)
    assert p22 == [2*f for f in TOP]
    i4 = [F(a, 2) for a in p44]
    # P23 <= 1 + w0123; P34 <= 1 + I4. The remainders are the
    # three-point capacities on the respective initial completion triples.
    triangle = [int({0, 1} <= w and len({2, 3, 4} & w) == 2) for w in WEDGES]
    assert [a-b for a, b in zip(p23, TOP)] == triangle
    assert [a-b for a, b in zip(p34, i4)] == triangle
    check_dual(triangle, 1, [('pair', (5, 6), 1, 1)])
    four = [('four_set', tuple(i for i in (2, 3, 4, 5, 6) if i != k), 1, 1)
            for k in (2, 3, 4, 5)]
    check_dual([a+b for a, b in zip(i4, HIGHEST)], 4, four)
    # Shared trace is optional for transport. It yields an additional
    # weighted inequality on every signed or unweighted comparison.
    others = [('directed_link', (6, 0), 2, F(1, 2)),
              ('four_set', (1, 3, 4, 5), 1, F(1, 2))]
    check_dual([a+F(b, 2) for a, b in zip(i4, SHARED)], 4,
               others + [(k, l, c, F(1) if l == (3, 4, 5, 6) else F(1, 2))
                         for k, l, c, unused in four])
    # Unit references for the four coupons and the complete floor.
    for matrix, ref in ((p22, 2), (p23, 2), (p34, 3), (p44, 4)):
        assert sum(x*y for x, y in zip(matrix, REF)) == ref
    assert directed_prefix(5, 5) == [2*v for v in HIGHEST]


def transport_example():
    alpha, beta, gamma, a, b, c, d = map(F, (72, 8, 6, '21/8', '5/2', '3/2', 1))
    h, k, q, p = alpha-beta, beta-gamma, gamma-a, a-b
    g, delta = h*q, k*(h+k+q)
    coupon = p*(a-c) + (b-d)*(c-d)
    room = q*(delta + k*(q+3*a-b-c-d)) - k*g/2
    assert room == k*q*(h/2+k+2*q+3*a-b-c-d)
    assert room >= delta*q/2
    assert p*(p+q) == F(7,16) < c*d
    assert b*(c-d) < c*d and F(101,100) < c/d < 2
    assert coupon == F(57,64) < d*d
    assert coupon + p*q/2 == F(141,128) > d*d
    assert g-b*(h+3*q)-5*b*b/2 > 0
    assert (h+k+q)*(d*d-coupon) < b*c*d+p*room/k


if __name__ == "__main__":
    verify_prefixes()
    transport_example()
    print("Verified the weighted five-tail prefix bounds, both occupancy prices and the strict split example.")

