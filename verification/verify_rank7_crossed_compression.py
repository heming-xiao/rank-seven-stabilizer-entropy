"""Exact mask, trace-price, and crossed-cut example checks for rank seven."""

from fractions import Fraction as F
from itertools import permutations

from verify_rank7_low_head_tail_prices import (
    CAPS, HIGHEST, REF, ROWS, TOP, WEDGES, verify_dual,
)


DUAL_11 = ((5, '1/2'), (11, '1/2'), (12, '1/4'), (13, '1/4'), (18, '1/4'),
           (19, '1/4'), (36, '3/2'), (37, '3/2'), (77, '3/4'), (88, '3/4'),
           (95, '5/4'), (96, '9/4'), (97, '9/4'))
DUAL_19 = ((5, '1'), (12, '5/8'), (13, '1/8'), (18, '5/8'), (19, '1/8'),
           (24, '5/8'), (25, '1/8'), (30, '1/2'), (36, '13/8'), (37, '17/8'),
           (77, '5/4'), (90, '1/8'), (93, '1/8'), (95, '1/8'), (97, '1/8'))


def mask_checks():
    family = [{0, 1, 2, 3}, {0, 1, 4, 5}, {2, 3, 4, 5}]
    family += [set(hi + lo) for hi in ((0, 2), (0, 3), (1, 2), (1, 3))
               for lo in ((4, 6), (5, 6))]
    small = {frozenset(i) for i in family}
    large = set()
    for destination in permutations((3, 4, 5)):
        move = dict(zip((3, 4, 5), destination))
        large.update(frozenset(move.get(i, i) for i in w) for w in small)
    assert len(small) == 11 and len(large) == 19
    degree4 = [int({0, 1} <= w and 6 not in w) for w in WEDGES]
    for good, n, e, dual, outside_peaks in (
        (small, F(3, 4), 4, DUAL_11, ((0, 2, 4, 6), (2, 3, 4, 5))),
        (large, F(5, 4), 0, DUAL_19, ((0, 2, 3, 6), (2, 3, 4, 5))),
    ):
        cost = [int(w not in good) + n + e*top + 4*i4
                for w, top, i4 in zip(WEDGES, TOP, degree4)]
        cap = verify_dual(dual, ROWS, CAPS, cost)
        assert cap == 7*n+e+8 == sum(x*y for x, y in zip(cost, REF))
        inside = [tuple(sorted(w)) for w in good if {0, 1} <= w]
        outside = [tuple(sorted(w)) for w in good if not {0, 1} <= w]
        assert (0, 1, 4, 5) in inside and all(componentwise(i, (0, 1, 4, 5)) for i in inside)
        assert all(i in outside for i in outside_peaks)
        assert all(any(componentwise(p, w) for p in outside_peaks) for w in outside)


def componentwise(a, b):
    return all(x <= y for x, y in zip(a, b))


def crossed_checks():
    outside6 = [{i, 2, 3, j} for i in (0, 1) for j in (4, 5, 6)]
    for w in WEDGES:
        key = tuple(sorted(w))
        if {0, 1} <= w:
            assert componentwise(key, (0, 1, 5, 6))
        elif w not in outside6:
            assert componentwise((0, 2, 4, 5), key)
        if 0 in w and (1 in w or 2 in w):
            assert componentwise(key, (0, 2, 5, 6))
        elif w not in outside6:
            assert any(componentwise(p, key) for p in ((0, 3, 4, 5), (1, 2, 4, 5)))
    t = tuple(map(F, (8, 5, 3, '8/5', '3/2', '6/5', 1)))
    alpha, beta, gamma, a, b, c, d = t
    u1, l1 = alpha*beta*c*d, alpha*gamma*b*c
    us, ls = alpha*gamma*c*d, max(alpha*a*b*c, beta*gamma*b*c)
    assert alpha*gamma*a*b > u1 and beta*gamma*a*b > us
    assert (u1-l1)**2/(2*(u1+l1)) > F(1, 8)
    assert (us-ls)**2/(2*(us+ls)) > F(1, 35)
    assert (u1-l1)**2/(4*l1) <= F(2, 15)
    assert (us-ls)**2/(4*ls) <= F(3, 100)
    frame = [F(ref, 2) if 3 in w else F(ref) for ref, w in zip(REF, WEDGES)]
    assert sum(value for w, value in zip(WEDGES, frame) if w in outside6) == 0
    assert sum(value for w, value in zip(WEDGES, frame) if {0, 1} <= w) == F(3, 2)
    assert sum(value for w, value in zip(WEDGES, frame) if 0 in w and (1 in w or 2 in w)) == F(5, 2)


def regression():
    from math import isqrt
    t = tuple(map(F, ('22.7', '8.075', '7.68', '1.8221', '1.822', '1.725', 1)))
    alpha, beta, gamma, a, b, c, d = t
    h, k, q, p = alpha-beta, beta-gamma, gamma-a, a-b
    x, y = alpha-a, beta-a
    g, delta, triangle, cubic = h*q, k*x, y*q, x*y*q
    length = h+2*k+3*q
    rate = F(101, 100)*168
    shared = max(0, g-F(200, 11)*max(0, b*(c-d)-(gamma-c)*p))
    lam, mu = 30*shared/rate, 30*delta/rate
    completion = cubic-lam*(y+q)-mu*q
    anti = k*k*(k*k+(h*h+q*q)/2)
    omega = max(0, a*cubic-delta/3)/(c*g+2*a*cubic)
    u = alpha*gamma*c*d
    nominal = beta*gamma*b*c
    genuine = beta*gamma*a*b
    assert alpha*beta*c*d < alpha*gamma*b*c
    assert alpha*a*b*c < nominal < genuine < u
    assert (u-nominal)**2/(4*nominal) < 16
    assert beta*gamma*a < 144 and beta*gamma*c < 144 and a >= b >= c >= 1
    assert 96*96 < rate*completion
    lower = (u-nominal)**2/(2*(u+nominal))
    product = u*genuine
    precision = 10**9
    sqrt_lower = F(isqrt(product.numerator*precision**2 // product.denominator), precision)
    assert sqrt_lower**2 <= product
    upper = u+genuine-2*sqrt_lower
    old, new = [], []
    for n, v in ((1, 0), (1, F(1, 2)), (1, 1), (1, 2), (1, 4), (0, 1)):
        m = max(n, F(v)/2)
        peak = max(n, v)
        z = max(F(5, 2)*n, 2*v, 2*n+v)
        base = b*c*length*m+z
        base += peak*((g*g+F(45, 4)*shared**2)/(12*rate)+p**4+length*p**3+
                      (2*(g-lam)+(delta-mu)+3*triangle)*p*p)
        base += v*(F(45, 4)*delta**2+anti)/(F(5, 2)*rate)
        base -= c*(g-lam)*n+(delta-mu)*v
        new.append(base+96*omega*n*lower/rate)
        improvement = max(0, 2*n+v-3*m)*q if 9*x*y >= 14 else 0
        old.append(base+completion*p*peak+improvement+96*omega*n*upper/rate)
    assert min(new) > F(3, 10), float(min(new))
    assert min(old) < -F(3, 20), float(min(old))
    print("Crossing comparison: six exact margins > 3/10; separated-cut minimum < -3/20.")


if __name__ == "__main__":
    mask_checks()
    crossed_checks()
    regression()
    print("Verified both 35-column trace duals, all four extremal amplitudes and the strict physical crossing example.")

