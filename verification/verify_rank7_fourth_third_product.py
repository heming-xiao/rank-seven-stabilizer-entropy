"""Rational certificate for the fourth-gap product theorem on all ordered spectra."""

from fractions import Fraction as F
from itertools import combinations
import json
from math import prod

from verify_rank7_low_head_tail_prices import CAPS, CERT, REF, ROWS, TOP, TRIPLES, WEDGES, coefficient_table, verify_dual


RATE = F(4242, 25)
R = 24/RATE
Z = F(2, 5)
J = F(61, 5)/(F(5, 2)*RATE)
T = 13/(12*RATE)
TOP_C = F(9, 5)
SLOPE = 400/(11*RATE)


def scalar_checks():
    # The two pieces 0 <= Delta <= 9 and Delta >= 9.
    u0 = (1-R)*(1-Z)
    assert (u0-F(1, 27))**2/(4*J) < 2
    assert u0*u0/(4*J) < 2+F(1, 3)
    m = F(8, 9)
    gain_floor = 192*m*m*Z*Z
    assert gain_floor == F(16384, 675)
    tau_ratio = F(200, 11)/(12*m*m)*(1-1/TOP_C)*(1-Z/TOP_C)**2
    assert tau_ratio == F(1225, 2376) < F(13, 24)

    # bcL/8 >= sqrt(12g)/8. Compare squared positive quantities.
    u1 = 1-R-(1-2*R)*Z
    delta_debit = u1*u1/(4*J)
    assert delta_debit > 2
    assert (2*(delta_debit-2)*8)**2 < 12*gain_floor
    # The extremal tail choice is b=c=9/5.
    assert SLOPE*3*(TOP_C-1) < 2*((1-R)-(1-2*R)*Z)
    discriminant = (1-R-SLOPE)**2-4*(2*SLOPE)*(4*(1-2*R)*Z)
    assert discriminant < 0
    boundary = (1-R)*TOP_C-(1-2*R)*Z+SLOPE*TOP_C*(TOP_C-1)
    assert boundary**3 < 81*T*F(7, 8)**2*TOP_C**4


def positive_tied_gain_example():
    h, k, q, p, b, c = map(F, (20, "1/2", 4, "1/10", "11/10", "21/20"))
    a = b+p
    x, length, g = h+k+q, h+2*k+3*q, h*q
    delta = k*x
    gamma, beta = a+q, a+q+k
    spectrum = (beta+h, beta, gamma, a, b, c, 1)
    assert p*(p+q) == F(41, 100) > Z
    assert g-b*(h+3*q)-F(5, 2)*b*b == F(1671, 40)
    assert beta*c < gamma*a*b and (c-Z)*g > F(8, 9)*b*c*length
    discount = 1-p*(a-c)-(b-1)*(c-1)
    t = delta+F(5, 2)*(discount-p*q)
    assert 0 < t < 2*delta
    anti = k*k*(k*k+(h*h+q*q)/2)
    old = (168*delta-24*t)*discount-168*k*b*c
    old -= 168*p*k*q*((1-24*t/(168*delta))*x+q+3*a-b-c-1-h/2)
    old -= (12*(2*t*delta-t*t)+anti)/F(5, 2)+max(g*g/24, q**4/72)
    assert old > 94 > (g*g/24)*b*length/(10*g)

    weights = {s: F(m, 3) for m, labels in (
        (1, "015 025 026 124 135 136 145 234 235 236 246 356"),
        (2, "016 034 456"),
    ) for s in labels.split()}
    mass = [weights.get("".join(map(str, t)), 0) for t in TRIPLES]
    assert all(sum(v*f for v, f in zip(row, mass)) <= cap for row, cap in zip(ROWS, CAPS))
    for pair in combinations(range(7), 2):
        assert sum(f for w, f in zip(WEDGES, mass) if set(pair) <= w) <= F(7, 3)
    gain = sum((f-r)*prod(spectrum[i] for i in w) for f, r, w in zip(mass, REF, WEDGES))
    assert gain == F(11507, 15000)


def signed_fourth_gap_transport():
    table = coefficient_table()
    ordinary = json.loads(CERT.with_name("rank7_forward_coefficients.json").read_text(encoding="utf-8"))
    prices = {tuple(row["monomial"]): row["prices"] for row in ordinary["old_certificates"]}
    for m, cost in table.items():
        if 3 in m and sum(i < 3 for i in m) <= 1:
            assert verify_dual(prices[m], ROWS, CAPS, cost) == sum(v*f for v, f in zip(cost, REF))
    assert table[(3, 3, 3, 3)] == TOP
    for i in range(3):
        assert table[(i, 3, 3, 3)] == [(i+1)*v for v in TOP]
    # The p-linear coefficients below are linear in b,c,d.  Test their
    # three ordered-tail generating rays and enough p values for degree two.
    for b, c, d in ((1, 1, 1), (1, 1, 0), (1, 0, 0)):
        for p in (1, 2):
            a = b+p
            shared_x = a*p+(a-c)*(a-d)-(b-c)*(b-d)
            assert shared_x == p*(3*b-c-d)+2*p*p
            for tail in (b, c, d):
                shared = ((a-tail)*(2*a+tail-b-c-d) -
                          (b-tail)*(b+tail-c-d))
                assert shared == p*(3*b-tail-c-d)+2*p*p
                triangle = ((3*a-b-c-d)*(a-tail)+tail*(a-tail) -
                            (2*b-c-d)*(b-tail)-tail*(b-tail))
                assert triangle == p*(2*b-c-d+3*b-2*tail)+3*p*p
            triangle_x = (3*a-b-c-d)*a-(2*b-c-d)*b
            assert triangle_x == p*(2*b-c-d+3*b)+3*p*p

    b, c = F(6, 5), F(11, 10)
    h, k, q = 20, 2, 4
    x, y, g = h+k+q, k+q, h*q
    alpha, beta, gamma = b+x, b+y, b+q
    cap = x*y*q-R*g*(y+q)-R*k*x*q
    assert beta*c > gamma*b*b and gamma > b*b and alpha*c > beta*b*b
    assert alpha**2*beta*c*(gamma+b)**2/gamma < 220**2
    assert alpha**2*gamma*c*c < 100**2
    assert gamma**2*alpha*c*(beta+b)**2/beta < 100**2
    assert RATE*cap > 96*(220+200)


if __name__ == "__main__":
    scalar_checks()
    positive_tied_gain_example()
    signed_fourth_gap_transport()
    print("Verified the product theorem, example and coefficientwise fourth-gap transport exactly.")
