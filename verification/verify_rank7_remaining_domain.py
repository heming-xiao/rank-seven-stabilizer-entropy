"""Check the rational bounds in the rank-seven remaining-domain reduction."""
from fractions import Fraction as F


def main():
    joint_coefficient = F(122, 25)
    center = 144 / (2 * joint_coefficient)
    ceiling = joint_coefficient * center**2
    slope = F(200, 101)
    root_bound = F(1101, 100)
    checks = {
        "third-to-fourth gap": 17**4 > 72 * ceiling,
        "fifth probability": 17**2 + 8 * center < 21**2,
        "middle gaps": 17**2 + 4 * center < 19**2,
        "Cauchy–Schwarz root": root_bound**2 > slope**2 + 24 * joint_coefficient,
        "top gap": F(100, 101) * center * (slope + root_bound) < 190,
        "normalization": 190 + 19 + 1 + 21 == 231,
    }
    for part, passed in checks.items():
        if not passed:
            raise ArithmeticError(f"Remaining-domain bound failed: {part}")
    print(f"Verified {len(checks)} remaining-domain bounds exactly.")


if __name__ == "__main__":
    main()

