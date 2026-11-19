"""Exact scalar certificate for all rank-seven spectra with fifth weight >= 3d."""

from fractions import Fraction as F
from itertools import combinations
from math import prod

from verify_rank7_low_head_tail_prices import CAPS, REF, ROWS, TRIPLES, WEDGES


RATE = F(4242, 25)
RHO = 1-24/RATE
GEOMETRY = F(5, 2)
J = (12+F(1, 5))/(GEOMETRY*RATE)


def maximum(linear, quadratic):
    return linear**2/(4*quadratic)


def verify_nonpositive_branch():
    threshold = F(18, 25)
    assert RHO == F(607, 707) and J == F(61, 2121)
    assert maximum(RHO, 9*J) < threshold
    assert F(9*13**2)/(12*RATE) > threshold

    def middle(x):
        return x/2-x**3/(24*(x+F(5, 2)))

    assert middle(F(2)) == F(25, 27) > threshold
    assert middle(F(25, 2)) == F(475, 576) > threshold
    assert F(25, 4)*(1-F(13, 15)) == F(5, 6) > threshold
    assert F(2)**2/(12*(2+F(5, 2))) == F(2, 27)
    price = F(25, 54)
    ratio = 1/(4*price*(1-price))
    assert ratio == F(729, 725) and ratio*threshold < 1
    # Both sides are quadratics in w,m, hence the three coordinates below
    # suffice for the homogeneous identity proving V <= ratio*m^2.
    for w, m in ((F(1), F(0)), (F(0), F(1)), (F(1), F(1))):
        x = (m-w)/price
        assert ratio*m*m-w*(w+x) == ratio*(m-2*(1-price)*w)**2


def verify_positive_branch():
    quad = F(122, 25)
    gain = F(299, 2)
    assert (12+F(1, 5))/GEOMETRY == quad
    assert 66 > (F(299, 18)-F(17, 2))**2
    peak = maximum(144, quad)
    assert peak == F(64800, 61) < F(160**2, 24)
    assert peak < 504*F(13, 50)+gain**2/24
    assert F(13, 50)+F(160, 3)-F(15, 2) < 47
    assert maximum(144-F(504, 47), quad) < gain**2/24


def verify_head_cone():
    assert maximum(RHO, J) < F(13, 2)
    h, k, q, p, b, c = map(F, (8, "3/2", "1/2", "1/40", "7/5", "11/10"))
    a = b+p
    x, length = h+k+q, h+2*k+3*q
    g, delta = h*q, k*x
    gamma, beta = a+q, a+q+k
    spectrum = (beta+h, beta, gamma, a, b, c, 1)
    assert q < b/2 and b*c*(h+4*k+3*q) > 22 and 5*g > b*length
    assert beta*c < gamma*a*b and gamma < a*b

    # Optimized weighted residual, in the earlier 168 normalization.
    discount = 1-p*(a-c)-(b-1)*(c-1)
    t = delta+GEOMETRY*(discount-p*q)
    assert 0 < t < 2*delta
    actual_anti = k*k*(k*k+(h*h+q*q)/2)
    remainder = (168*delta-24*t)*discount-168*k*b*c
    remainder -= 168*p*k*q*((1-24*t/(168*delta))*x+q+3*a-b-c-1-h/2)
    remainder -= (12*(2*t*delta-t*t)+actual_anti)/GEOMETRY+max(g*g/24, q**4/72)
    assert remainder > 511 and (g*g/24)*b*length/(10*g) < 1
    assert g-b*(h+3*q)-F(5, 2)*b*b < 0

    groups = ((1, "035 045 134 135 145"), (2, "015 025 026 124 125 136 234 235 236 246 356"),
              (3, "034"), (4, "016 456"))
    weights = {s: F(count, 6) for count, labels in groups for s in labels.split()}
    wedge_weights = [weights.get("".join(map(str, triple)), 0) for triple in TRIPLES]
    assert all(sum(x*y for x, y in zip(row, wedge_weights)) <= cap for row, cap in zip(ROWS, CAPS))
    for pair in combinations(range(7), 2):
        assert sum(y for w, y in zip(WEDGES, wedge_weights) if set(pair) <= w) <= F(7, 3)
    gain = sum((v-r)*prod(spectrum[i] for i in w) for v, r, w in zip(wedge_weights, REF, WEDGES))
    assert gain == F(752983, 7680000) > 0


if __name__ == "__main__":
    verify_nonpositive_branch()
    verify_positive_branch()
    verify_head_cone()
    print("Verified b >= 3d, the alternate head cone, and its strict 119-row example exactly.")
