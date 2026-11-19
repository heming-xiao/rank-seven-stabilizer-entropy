"""Exact compactification of both scalar estimates in the small middle split."""

from fractions import Fraction as F
from math import comb

from verify_rank7_four_equal_tails import bernstein_grid


RATE = F(1, 96)


def multiply(a, b):
    out = [F(0)] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def quartic(second):
    # On the boundary write u=aa+bb/w and v=cc+dd*w.
    r = RATE
    s = 1-2*r
    aa, bb, cc, dd = (3, F(11, 2), 1, 1) if second else (3*s, 3*s, s, s)
    price = (2880 if second else 1440)*r
    uvw = [bb*cc, aa*cc+bb*dd, aa*dd]
    poly = multiply(uvw, uvw)
    for i, term in enumerate((0, bb, aa+cc+2*r-F(7, 5), dd)):
        poly[i] -= price*term
    return poly


def positive_halfline(coefficients):
    degree = len(coefficients)-1
    # t=w/(1+w). The resulting polynomial is expressed in the
    # ordinary power basis and tested on t in [0,1].
    compact = [F(0)]*(degree+1)
    for i, c in enumerate(coefficients):
        for j in range(degree-i+1):
            compact[i+j] += c*comb(degree-i, j)*(-1)**j
    root = bernstein_grid({(0,)*i:c for i, c in enumerate(compact)}, dimension=1)
    stack = [(root, 0)]
    leaves = depth = 0
    while stack:
        grid, level = stack.pop()
        if min(grid.values) > 0:
            leaves += 1
            depth = max(depth, level)
            continue
        assert level < 12
        stack.extend((half, level+1) for half in grid.halves(0))
    return leaves, depth


if __name__ == "__main__":
    for second in (False, True):
        coefficients = quartic(second)
        if second:
            assert [8*c for c in coefficients] == [242, -572, 213, 168, 72]
        print(f"{'Positive' if second else 'Nonpositive'} tied coefficient: "
              f"{positive_halfline(coefficients)} (leaves, depth).")

