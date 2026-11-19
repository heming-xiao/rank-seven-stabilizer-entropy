"""Check the extended scalar certificate for two tied leading pairs."""

from sympy import Rational, symbols

from verify_rank7_three_levels import initial_controls, positive_certificate


def main():
    z, u = symbols("z u")
    scaled_z = Rational(71, 100) * z
    r = scaled_z**2
    y = scaled_z + (1 - scaled_z) * u
    s_separated = r * y**2
    s_unseparated = r**2 * u

    def mixed_minus_gain(s):
        return 3 * ((1 - r)**2 + 4 * s**2)**2 - 168 * (1 - 2 * r - s) * s**2

    separated = mixed_minus_gain(s_separated) + 64 * r**2 * y**2 * (y - scaled_z)**2
    unseparated = mixed_minus_gain(s_unseparated)
    for name, polynomial in (
        ("s >= r^2", separated),
        ("s <= r^2", unseparated),
    ):
        leaf_count, minimum_control = positive_certificate(
            initial_controls(polynomial, z, u), max_depth=12
        )
        print(f"{name}: {leaf_count} certified rectangles, lower bound {minimum_control}")


if __name__ == "__main__":
    main()
