"""Exact certificates for the true-highest / nominal-shared fourth-gap transport."""

from sympy import Poly, Rational, expand, symbols

from verify_rank7_low_head_tail_prices import (
    CAPS, KNOWN_ROWS, REF, ROWS, WEDGES, verify_dual,
)


def certify_nonnegative(expression, gaps):
    coefficients = Poly(expression, *gaps).coeffs()
    assert all(value >= 0 for value in coefficients)
    return len(coefficients)


def main():
    # The top wedge and the three crossing wedges comprise one physical row.
    triple = [int({1, 2, 3} <= wedge) for wedge in WEDGES]
    row = KNOWN_ROWS.index(('four_set', (0, 4, 5, 6), 1))
    assert ROWS[row] == triple
    assert verify_dual([(row, '1')], ROWS, CAPS, triple) == 1
    assert sum(flag*ref for flag, ref in zip(triple, REF)) == 1

    d, tail1, tail2, size, h, k, extra = symbols("d tail1 tail2 p h k extra")
    gaps = (d, tail1, tail2, size, h, k, extra)
    c = d + tail1
    b = c + tail2
    a = b + size
    q = 2*d/3 + extra
    Y = k + q
    X = h + Y
    alpha0, gamma0 = b+X, b+q
    alpha, beta, gamma = a+X, a+Y, a+q
    A = Rational(4242, 25)
    S = c*d

    assert expand(gamma*h-alpha*q - (alpha*a-beta*gamma)) == 0
    assert expand(d*q-(b-d)*a - (d*gamma-a*b)) == 0
    # On the A branch the squared prefactor of the q bound has
    # nonnegative headroom alpha/a * (alpha*a - beta*gamma).
    assert expand(a*alpha**2-alpha*beta*gamma-alpha*(alpha*a-beta*gamma)) == 0
    assert expand((alpha-alpha0)*q-size*q) == 0
    assert expand((gamma-gamma0)*h-size*h) == 0
    # h<q implies gamma*h <= alpha*q for every p.
    assert expand(alpha*q-gamma*h - (gamma*(q-h)+(alpha-gamma)*q)) == 0

    # Check the entire exterior polynomial divided by p, at the largest
    # allowed shifts. Lower shifts only increase its coefficients.
    g, delta = h*q, k*X
    lam, mu = 36*g/A, 42*delta/A
    L = h+2*k+3*q
    cubic = X*Y*q-lam*(Y+q)-mu*q
    polynomial = A*(cubic + size**3 + L*size**2
                    + (g-lam)*(2*size+2*b-c-d)
                    + (delta-mu)*(size+b-c)
                    + Y*q*(3*size+3*b-c-d))
    kept = (A-78)*alpha0*Y*q + (A-36)*h*q*(b-c) + 3*A*Y*q*size
    exterior_count = certify_nonnegative(polynomial-kept, gaps)

    # This rational upper bound includes two integrated widths and
    # the increase of the purchased crossing, in normalized units.
    zeta_upper = Rational(27, 50)
    assert (4-zeta_upper)**2 < 12 and zeta_upper < 4
    denominator = b*(b+q)
    joined = (96*zeta_upper*alpha0*S*k*(b+q) + 24*alpha0*S*q**2
              + 48*d*(alpha0*q+size*q+h*(b-c))*denominator)
    rate_count = certify_nonnegative(kept*denominator-joined, gaps)

    assert (A-78)*Rational(2, 3) == Rational(1528, 25)
    assert 48+24*Rational(2, 5) == Rational(288, 5)
    assert (A-78)*Rational(2, 3) > max(96*zeta_upper, Rational(288, 5))
    assert (A-36)*Rational(2, 3) > 48 and 3*A*Rational(2, 3) > 48
    print(f"Verified shared completion and active arms, {exterior_count} exterior "
          f"and {rate_count} combined payment coefficients.")


if __name__ == "__main__":
    main()
