"""Exact certificate allowing arbitrary fifth-largest probability."""

import sys
from fractions import Fraction as F

from verify_rank7_near_three_tails import U, OUTER, objectives
from verify_rank7_four_equal_tails import EXTERIOR_RATE, GEOMETRY, HIGHEST, RESIDUAL, SHARED, verify_cover
from verify_rank7_three_equal_tails import RAYS


EDGES = tuple(map(F, ("1.01", "1.02", "1.04", "1.07", "1.1", "1.2", "1.4", "1.7", "2.1", "2.8", "4", "6", "10")))


def verify_outer_strip(n, v, low, high):
    m = max(n, F(v) / 2)
    p = max(n, v)
    z = max(F(5, 2) * n, 2 * v, 2 * n + v)
    tau = F(200, 11) * high * (U - 1)
    linear = U * RESIDUAL * n + F(15, 8) * tau * p / EXTERIOR_RATE
    spent = linear**2 / (4 * SHARED * p) + U * n * (1 - RESIDUAL) * tau
    spent += RESIDUAL**2 * v / (4 * (HIGHEST + 1 / (5 * GEOMETRY * EXTERIOR_RATE)))
    assert OUTER * low * m + z >= spent, (n, v, low, high)


def verify_big_b():
    # On E>0, q+2k/c > b, hence L>b. For b>=10,
    # 1 <= b/10 before completing the shared square and b <= b^2/10.
    tau_ratio = F(200, 11) * (U - 1)
    for n, v in RAYS:
        m = max(n, F(v)/2)
        p = max(n, v)
        linear = U * RESIDUAL * n / 10 + F(15, 8) * tau_ratio * p / EXTERIOR_RATE
        share = linear**2 / (4 * SHARED * p)
        constant = U * n * (1-RESIDUAL) * tau_ratio / 10
        other = RESIDUAL**2 * v / (400 * (HIGHEST + 1 / (5 * GEOMETRY * EXTERIOR_RATE)))
        assert m >= share + constant + other


def verify_strip(low, high, c_low, c_high):
    accepted = outside = depth = 0
    for n, v in RAYS:
        verify_outer_strip(n, v, low, high)
        polynomials, choices = objectives(n, v, c_low, c_high, low, high)
        counts, out, deep = verify_cover((n, v), polynomials, choices, 38, dimension=4)
        accepted += sum(counts)
        outside += out
        depth = max(depth, deep)
    return accepted, outside, depth


if __name__ == "__main__":
    verify_big_b()
    bounds = (F(1), (1 + U) / 2, U)
    for i, (low, high) in enumerate(zip(EDGES, EDGES[1:])):
        if len(sys.argv) > 1 and i not in map(int, sys.argv[1:]):
            continue
        for c_low, c_high in zip(bounds, bounds[1:]):
            result = verify_strip(low, high, c_low, c_high)
            print(f"b=[{low},{high}], c=[{c_low},{c_high}]: {result}", flush=True)

