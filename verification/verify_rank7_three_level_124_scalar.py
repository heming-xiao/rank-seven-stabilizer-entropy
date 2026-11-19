"""Verify the scalar payment for the rank-seven 1+2+4 spectrum.

The conditional comparison assumes nu <= 16*kappa in the positive-gain
region. The two polynomials separate the order of the third and fourth
four-exterior amplitude levels.
"""

from sympy import Rational, symbols

from verify_rank7_three_levels import initial_controls, positive_certificate


def below_crossing(z, u):
    r = z**2
    ratio = u / 2
    reference = r * (1 - r)
    mixed = Rational(3, 4) * (1 - (1 - r) * ratio + 16 * reference * ratio**2) ** 2
    exterior = 48 * ratio**2 * r * (1 - z) ** 2
    gain = 168 * ratio**2 * reference * (
        1 - (2 + r) * ratio + reference * ratio**2 / 2
    )
    return mixed + exterior - gain


def above_crossing(z, u):
    root_r = Rational(3, 5) * z
    r = root_r**2
    root_ratio = root_r + (Rational(71, 100) - root_r) * u
    mixed = Rational(3, 4) * (
        (1 - r) * (1 - root_ratio**2) + 16 * r * root_ratio**4
    ) ** 2
    exterior = 48 * r * root_ratio**4 * (
        (1 - root_ratio) ** 2 + (root_ratio - root_r) ** 2
    )
    gain = 168 * r * root_ratio**4 * (
        (1 - r) - (2 + r) * root_ratio**2 + r * root_ratio**4 / 2
    )
    return mixed + exterior - gain


def main():
    z, u = symbols("z u")
    for name, polynomial in (
        ("s <= r^2", below_crossing(z, u)),
        ("s >= r^2", above_crossing(z, u)),
    ):
        controls = initial_controls(polynomial, z, u)
        count, bound = positive_certificate(controls, max_depth=18)
        print(f"{name}: {count} certified rectangles, lower bound {bound}")


if __name__ == "__main__":
    main()
