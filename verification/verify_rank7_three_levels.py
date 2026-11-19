"""Check the three rational Bernstein certificates for rank-seven spectra.

These certificates cover all four middle-level multiplicities when the
two largest probabilities are one. Requires SymPy for polynomial expansion;
all Bernstein arithmetic thereafter uses fractions.Fraction.
"""

from fractions import Fraction
from math import comb

from sympy import Poly, Rational, symbols


def initial_controls(expression, z, u):
    polynomial = Poly(expression, z, u)
    degree_z, degree_u = polynomial.degree_list()
    coefficients = {
        index: Fraction(value) for index, value in polynomial.terms()
    }
    return tuple(
        tuple(
            sum(
                coefficients.get((i, j), 0)
                * Fraction(comb(k, i), comb(degree_z, i))
                * Fraction(comb(l, j), comb(degree_u, j))
                for i in range(k + 1)
                for j in range(l + 1)
            )
            for l in range(degree_u + 1)
        )
        for k in range(degree_z + 1)
    )


def bisect_controls(values):
    values = list(values)
    left = [values[0]]
    right = [values[-1]]
    while len(values) > 1:
        values = [(a + b) / 2 for a, b in zip(values, values[1:])]
        left.append(values[0])
        right.append(values[-1])
    return tuple(left), tuple(reversed(right))


def bisect_patch(controls, axis):
    rows = zip(*controls) if axis == 0 else controls
    parts = tuple(zip(*(bisect_controls(row) for row in rows)))
    if axis == 0:
        return tuple(tuple(zip(*part)) for part in parts)
    return parts


def positive_certificate(controls, max_depth):
    pending = [(controls, 0)]
    leaves = []
    while pending:
        patch, depth = pending.pop()
        lower_bound = min(min(row) for row in patch)
        if lower_bound > 0:
            leaves.append(lower_bound)
            continue
        if depth == max_depth:
            raise ArithmeticError(f"Unproved patch at depth {depth}: {lower_bound}")
        for child in bisect_patch(patch, depth % 2):
            pending.append((child, depth + 1))
    return len(leaves), min(leaves)


def main():
    z, u = symbols("z u")

    # Middle multiplicity three or four. Original z is sqrt(r) and the
    # tested range x >= z is parameterized by x = z + (1-z)u.
    z_small = Rational(3, 5) * z
    r = z_small**2
    x = z_small + (1 - z_small) * u
    common = (
        3 * ((1 - r)**2 + 4 * r**2 * x**2)**2
        + 64 * r**2 * (x - z_small)**2
        - 168 * (1 - 3 * r) * r**2 * x**2
    )

    # Middle multiplicity two. Write y = sqrt(s/r). The original intervals
    # are [0,3/5] for sqrt(r) and [7/10,1] for y.
    y = Rational(7, 10) + Rational(3, 10) * u
    s = r * y**2
    two = (
        3 * ((1 - r)**2 + 4 * s**2)**2
        + 64 * r**2 * y**2 * (y - z_small)**2
        - 168 * (1 - 2 * r - s) * s**2
    )

    # Middle multiplicity one. Original z is sqrt(r), and
    # x = 2s/(1-r). Both lie in [0,1].
    d = 1 - z**2
    one = (
        3 * (1 + d * (u**2 - u / 2))**2
        + 16 * u**2 * (1 - z)**2
        - 42 * d * u**2 * (1 - u)
    )

    for name, expression, max_depth in (
        ("2+3+2 and 2+4+1", common, 5),
        ("2+2+3", two, 7),
        ("2+1+4", one, 8),
    ):
        leaf_count, lower_bound = positive_certificate(
            initial_controls(expression, z, u), max_depth
        )
        print(f"{name}: {leaf_count} certified rectangles, lower bound {lower_bound}")


if __name__ == "__main__":
    main()
