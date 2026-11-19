"""Verify the exact algebraic certificates for rank-seven t1=t2 optimality."""

from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import prod
from operator import xor

from sympy import Poly, Rational, expand, symbols

from verify_rank7_arbitrary_tied_head_scalar import initial_controls, positive_certificate
from verify_rank7_equal_floor_packing import main as verify_packing
from verify_rank7_four_level_1231_scalar import large_defect, matchings, verify_matching_charge


def verify_rank_six_endpoint():
    h, q, p, t, c = gaps = symbols("h q p t c")
    b = c + t
    a = b + p
    r = a + q
    weights = (r + h, r, r, a, b, c)
    vertices = tuple(range(6))
    labels = set(vertices)
    exterior = {}
    shared = {}
    reference = []
    for pair in combinations(vertices, 2):
        wedge = labels.difference(pair)
        exterior[pair] = prod(weights[i] for i in wedge)
        shared[pair] = sum(
            prod(weights[i] for i in wedge.difference({0, partner}))
            for partner in (1, 2)
            if {0, partner} <= wedge
        )
        if reduce(xor, wedge) == 0:
            reference.append(pair)
    if len(reference) != 3:
        raise ArithmeticError("Unexpected computational reference")
    exterior_ref = sum(exterior[pair] for pair in reference)
    shared_ref = sum(shared[pair] for pair in reference)
    all_matchings = matchings(vertices)
    if len(all_matchings) != 76:
        raise ArithmeticError("Incomplete rank-six matching enumeration")
    for matching in all_matchings:
        shared_loss = shared_ref - sum(shared[pair] for pair in matching)
        exterior_loss = exterior_ref - sum(exterior[pair] for pair in matching)
        adjusted_loss = exterior_loss - (h * q / 2) * shared_loss
        for loss in (shared_loss, adjusted_loss):
            if any(value < 0 for value in Poly(loss, *gaps).coeffs()):
                raise ArithmeticError(f"Unproved rank-six endpoint for {matching}")
    print("Rank-six weighted endpoint: 152 exact matching comparisons")


def verify_scalar_and_rounding():
    x, y, z = symbols("x y z")
    u = x - 4
    polynomial = Rational(39, 4) * x**4 - 432 * x**2 + 1008 * x + 564
    lower_bound = 36 * (u + Rational(2, 3))**2 + 164
    remainder = u**2 * (Rational(39, 4) * x**2 + 78 * x)
    if expand(polynomial - lower_bound - remainder) != 0:
        raise ArithmeticError("Invalid certificate for the small-defect quartic")
    print("Small-defect quartic: analytic certificate with lower bound 164")

    if not (
        2 * Fraction(1, 7) * Fraction(6, 7)**2 > Fraction(5, 24)
        and 2 * Fraction(11, 14) * Fraction(27, 28) == Fraction(297, 196)
        and Fraction(18 * 196, 297) < 12
    ):
        raise ArithmeticError("Invalid shared-anchor rounding constants")
    print("Shared-anchor rounding constants verified")

    degrees, controls = initial_controls(Poly(large_defect(x, y, z), x, y, z))
    count, bound = positive_certificate(degrees, controls, max_depth=21)
    print(f"Large-defect scalar: {count} exact boxes, lower bound {bound}")


def main():
    verify_packing()
    verify_rank_six_endpoint()
    verify_matching_charge()
    verify_scalar_and_rounding()


if __name__ == "__main__":
    main()
