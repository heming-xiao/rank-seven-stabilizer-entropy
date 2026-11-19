"""Exact scalar and row checks for two unrestricted nominal compression widths."""
from fractions import Fraction as F
from math import comb

from verify_rank7_low_head_tail_prices import CAPS, KNOWN_ROWS, REF, ROWS, WEDGES, verify_dual
from verify_rank7_harmonic_tail_transport import directed_prefix


RATE = F(101, 100)*168


def crossing_rows():
    a3 = [int(w == {0, 1, 2, 3}) for w in WEDGES]
    a4 = [int(w == {0, 1, 2, 4}) for w in WEDGES]
    m4 = [int(w in ({0, 2, 3, 4}, {1, 2, 3, 4})) for w in WEDGES]
    cost = [a+b+m for a, b, m in zip(a3, a4, m4)]
    row = KNOWN_ROWS.index(('pair', (5, 6), 1))
    assert verify_dual(((row, '1'),), ROWS, CAPS, cost) == sum(x*y for x, y in zip(cost, REF)) == 1
    mass = [int(2 in w and 3 in w and 4 <= max(w) and
                ((0 in w) != (1 in w))) for w in WEDGES]
    cost = [m+2*a for m, a in zip(mass, a3)]
    rows = [KNOWN_ROWS.index(('four_set', tail, 1)) for tail in ((1, 4, 5, 6), (0, 4, 5, 6))]
    assert verify_dual([(i, '1') for i in rows], ROWS, CAPS, cost) == sum(x*y for x, y in zip(cost, REF)) == 2
    i3 = [F(v, 2) for v in directed_prefix(3, 3)]
    assert [m+i for m, i in zip(m4, i3)] == ROWS[row]
    pair46 = KNOWN_ROWS.index(('pair', (4, 6), 1))
    cost = [v+m for v, m in zip(directed_prefix(2, 4), m4)]
    assert verify_dual(((row, '1'), (pair46, '1')), ROWS, CAPS, cost) == sum(x*y for x, y in zip(cost, REF)) == 2


def tied_payment(eta, z):
    return ((RATE-48)*eta/5*(1+1/(5*z)) +
            (RATE-24)*(eta-1)*(z+F(1, 5))/(z+F(6, 5)))


def tied_width_extension():
    for z in map(F, (1, 2, 3)):
        large = F(6)*(26925*z*z-28355*z+18252)/(3125*z*(5*z+6))
        assert tied_payment(F(6, 5), z)-48 == large
    assert 28355**2 < 4*26925*18252
    small = F(7, 25)
    assert (RATE-48)*F(11, 50)*(1+1/(5*small)) > 45
    assert 48*(1-F(3, 25)/small) < 28

    # Multiplying through by positive denominators leaves a polynomial
    # of degree at most five. Six distinct evaluations prove the identity.
    coeff = (625564, -2637822, 392532, 13769553, 13967352, 3797892)
    for w in map(F, range(6)):
        z = F(42, 25)*(1+w)**2-F(7, 5)
        difference = tied_payment(F(11, 10), z)-96*(1-F(3, 25)/z)/(2+w)
        denominator = 4375*(w+2)*(6*w*w+12*w+1)*(42*w*w+84*w+37)
        assert difference*denominator == 12*sum(c*w**i for i, c in enumerate(coeff))
    split = F(1, 4)
    lower = [sum(coeff[i]*split**i*comb(5-i, j-i) for i in range(j+1))
             for j in range(6)]
    upper = [sum(coeff[i]*split**(i-j)*comb(i, j) for i in range(j, 6))
             for j in range(6)]
    assert min(lower) > 0 and min(upper) > 0


def spectral_checks():
    # Full-width constants for the strict and tied cones.
    assert (RATE-48)*F(8, 5) > 192
    assert (RATE-48)*F(2, 5) > 48
    assert RATE-24 > 144
    for raw, tied in (
        (('9.5', '5.8', '3.6', '1.6', '1.5', '1.2', 1), False),
        (('6.6', '3.9', '2.3', '1.5', '1.5', '1.2', 1), True),
    ):
        alpha, beta, gamma, a, b, c, d = map(F, raw)
        q = gamma-a
        assert beta*d > gamma*b and beta*c*d < gamma*a*b
        assert gamma*d > a*b and alpha*d > beta*b and alpha*c*d < beta*a*b
        if tied:
            assert a == b and q > max(b/5, 2*d/5)
        else:
            assert a > b and q > max(a, 8*d/5)


if __name__ == '__main__':
    crossing_rows()
    spectral_checks()
    tied_width_extension()
    print("Verified the mass and prefix rows, strict double crossings, and full tied widths for b >= 11d/10.")

