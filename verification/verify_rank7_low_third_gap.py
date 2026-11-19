"""Exact single-highest-cut certificate for gamma-a <= 3d/5, with all four tails free."""

from fractions import Fraction as F

from verify_rank7_four_equal_tails import multiply, sum_polynomials, verify_cover


RATE = F(4242, 25)
RHO = 1-F(30)/RATE
J = (F(45, 4)+F(1, 5))/(F(5, 2)*RATE)


def objectives(extension=False):
    one = {(): 1}
    scales = (36, 6, F(1, 15), F(2, 3), F(199, 100)) if extension else (28, F(28, 5), F(3, 5), F(2, 3), 2)
    h, k, q, p, spread = ({(i,): u} for i, u in enumerate(scales))
    def total(*polys):
        return sum_polynomials(*[(1, poly) for poly in polys])

    floor = F(101, 100) if extension else F(1)
    if extension:
        q = sum_polynomials((F(3, 5), one), (1, q))
    b = sum_polynomials((floor, one), (1, spread))
    a = total(b, p)
    x = total(h, k, q)
    gamma = total(a, q)
    beta = total(gamma, k)
    alpha = total(beta, h)
    delta = multiply(k, x)
    hp3q = sum_polynomials((1, h), (3, q))
    denom = sum_polynomials((floor, hp3q), (F(5, 2)*floor**2, one))
    theta_num = sum_polynomials((1, denom), (-1, multiply(h, q)))
    bare = sum_polynomials(
        (floor, multiply(b, k)), (-RHO, delta), (RHO, multiply(delta, p, total(p, q))),
        (J, multiply(delta, delta)),
    )
    if extension:
        anti = multiply(k, k, sum_polynomials(
            (1, multiply(k, k)), (F(1, 2), multiply(h, h)), (F(1, 2), multiply(q, q)),
        ))
        bare = sum_polynomials((1, bare), (1/(F(5, 2)*RATE), anti),
                               (-1/(F(25, 2)*RATE), multiply(delta, delta)),
                               (1/(12*RATE), multiply(h, h, q, q)))
    singleton = sum_polynomials((2, one), (floor/2, multiply(b, hp3q)))
    base = total(multiply(denom, bare), multiply(theta_num, singleton))
    outside = multiply(gamma, a, b)
    inner = sum_polynomials((floor, beta))
    gap = sum_polynomials((1, inner), (-1, outside))
    combined = sum_polynomials(
        (1, multiply(total(inner, outside), base)),
        (32/RATE, multiply(denom, alpha, gap, gap)),
    )
    return (base, gap, combined)


def main():
    assert RHO**2/(4*J) < F(32, 5)
    assert RHO < 1 and F(12, 5)*2+F(8, 5) == F(32, 5)
    assert 1-F(2, 3)*(F(2, 3)+F(3, 10)) == F(16, 45)
    assert (RHO*F(16, 45))**2/(4*J) < F(4, 5)
    assert (RHO*F(5, 9))**2/(4*J) < F(21, 10)
    assert RHO*F(5, 9) < F(7, 5)
    counts, outer, depth = verify_cover(
        (0, 1), objectives(), ((0,), (1, 2)), 64, dimension=5, outer_faces=((0, 1),),
    )
    print(f"Low third gap: {counts} base/cut leaves, {outer} analytic leaves, depth {depth}.")
    assert 1-F(2, 3)*(F(2, 3)+F(3, 5)) == F(7, 45)
    assert (F(7, 45)*RHO)**2/(4*J) < F(2, 3)
    assert 5*(F(7, 3))**2 > (F(32, 5)-F(14, 9))**2
    assert 5*RHO**2 < F(7, 3)**2 and F(20, 3) > F(32, 5)
    counts, outer, depth = verify_cover(
        (0, 1), objectives(True), ((0,), (1, 2)), 64, dimension=5, outer_faces=((0, 1),),
    )
    print(f"Upper extension: {counts} base/cut leaves, {outer} analytic leaves, depth {depth}.")


if __name__ == "__main__":
    main()
