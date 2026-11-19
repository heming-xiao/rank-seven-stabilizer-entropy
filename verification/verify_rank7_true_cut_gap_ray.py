"""Check the physical trace row and derivative bounds for both true cuts."""

from fractions import Fraction as F
from math import prod

import sympy as sp

from verify_rank7_low_head_tail_prices import CAPS, HIGHEST, KNOWN_ROWS, REF, ROWS, SHARED, TOP, WEDGES, verify_dual


def shared_trace_row():
    shared_cut = [int(0 in w and bool({1, 2} & w)) for w in WEDGES]
    target = [s+t for s, t in zip(shared_cut, TOP)]
    keys = [('directed_link', (3, 0), 2), ('four_set', (1, 4, 5, 6), 1),
            ('four_set', (2, 4, 5, 6), 1)]
    prices = [(KNOWN_ROWS.index(key), '1') for key in keys]
    assert verify_dual(prices, ROWS, CAPS, target) == sum(x*y for x, y in zip(target, REF)) == 4


def derivative_checks():
    xi, r = sp.symbols("xi r", positive=True)
    raw = (xi-r)*(2*r-1/xi)/(xi**2-1)
    boundary = raw.subs(r, 1).cancel()
    assert sp.simplify(boundary-(2-1/xi)/(1+xi)) == 0
    critical = (1+sp.sqrt(3))/2
    assert sp.simplify(sp.diff(boundary, xi).subs(xi, critical)) == 0
    assert sp.simplify(boundary.subs(xi, critical)-(4-2*sp.sqrt(3))) == 0
    rmax = xi/2+1/(4*xi)
    assert sp.simplify(sp.diff(raw, r).subs(r, rmax)) == 0
    assert sp.simplify(raw.subs(r, rmax)-F(1, 2)-1/(8*xi**2*(xi**2-1))) == 0
    effective = (2*r-1/xi)/(r+xi)
    assert sp.simplify(sp.diff(effective, r)*(xi+r)**2-(2*xi+1/xi)) == 0
    assert sp.simplify(effective.subs(r, xi)-(1-1/(2*xi**2))) == 0

    # Weighted active outside endpoint, including the ab/S correction.
    a, b, c, d, h, k, q = sp.symbols("a b c d h k q", positive=True)
    alpha, beta, gamma = a+h+k+q, a+k+q, a+q
    assert sp.expand(gamma*h-alpha*q-(alpha*a-beta*gamma)) == 0
    assert sp.simplify(alpha*c*(a*b/(c*d)-1)-alpha*(a-c)-alpha*a*(b-d)/d) == 0

    rate = F(4242, 25)
    assert 96/(rate-48) < F(4, 5)
    assert (4-F(27, 50))**2 < 12
    assert F(2, 5) > F(1, 2)**2
    assert 1-F(1, 2)/(1+F(1, 2)) > F(27, 50)
    assert F(3, 5)**2+F(8, 5) == F(7, 5)**2
    assert 72/(rate-48) < F(3, 5)
    assert 48/(rate-48) < 1
    # z=2/3, U is the positive root of U*(U-z)=2/5.
    assert F(21, 20)*(F(21, 20)-F(2, 3)) > F(2, 5)
    assert 1-1/(2*(1+F(21, 20))) == F(31, 41)
    assert 96*F(31, 41)/(rate-60) < F(2, 3) and 48/(rate-60) < 1


def seed_example():
    rate = F(4242, 25)
    a = b = F(26, 25)
    c, h, k, q = F(51, 50), 5, 1, F(3, 5)
    x, y, g = h+k+q, k+q, h*q
    delta = k*x
    alpha, beta, gamma = a+x, a+y, a+q
    spec = (alpha, beta, gamma, a, b, c, 1)
    tau = F(200, 11)*b*(c-1)
    anti = k*k*(k*k+(h*h+q*q)/2)
    assert (12*(2*(g-tau)-1)+g*g)/12 >= 4
    assert (12*(2*delta-1)+anti)/F(5, 2) >= 64
    omega = (a*x*y*q-delta/3)/(c*g+2*a*x*y*q)

    def above(scale, inside, outside, minimum):
        # scale*(sqrt(inside)-sqrt(outside))^2 > minimum, inside > outside.
        z = minimum/scale
        return inside > outside and inside+outside > z and (inside+outside-z)**2 > 4*inside*outside

    assert above(64*alpha, beta*c, gamma*a*b, F(46))
    assert above(96*omega*alpha, gamma*c, a*b*c, F(11))
    assert above(96*omega*gamma, alpha*c, beta*a*b, F(11))
    costs = []
    for w, n, v in zip(WEDGES, SHARED, HIGHEST):
        shared = sum(prod(spec[j] for j in w-pair) for pair in ({0, 1}, {0, 2}) if pair <= w)
        highest = prod(spec[j] for j in w-{0, 1}) if {0, 1} <= w else 0
        costs.append(rate*prod(spec[j] for j in w)-24*shared-24*highest-15*n-110*v)
    raw = [(1, 81597550), (12, 3033614325), (13, 1117184975), (18, 10395815325),
           (19, 3618085300), (24, 10395815325), (25, 3618085300), (30, 10659137475),
           (31, 3614341825), (32, 66464925), (36, 11031516261), (37, 3708972361),
           (38, 105370011), (48, 9940275), (50, 9940275), (73, 212661975),
           (74, 531377250), (75, 531377250), (76, 10101793315), (77, 2791219325),
           (93, 80764200), (94, 86513379), (95, 80764200), (96, 86513379), (97, 193639905)]
    dual = [(index, str(F(numer, 9765625))) for index, numer in raw]
    assert verify_dual(dual, ROWS, CAPS, costs) == sum(v*f for v, f in zip(costs, REF))


if __name__ == "__main__":
    shared_trace_row()
    derivative_checks()
    seed_example()
    print("Verified both true-cut transfer bounds and one complete fourth-gap ray exactly.")
