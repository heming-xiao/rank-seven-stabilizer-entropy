"""Verify the analytic scalars for the rank-seven large-fourth-gap theorem."""

from fractions import Fraction as F


def main():
    p = F(5, 7)
    discount = 1-p*p
    slope = F(5, 12)*p
    shared = 1-2*p*p/F(9, 5)
    end = discount/p
    upper = discount/slope

    def envelope(q):
        f = discount-slope*q
        return shared*q + 13*max(0,discount-p*q)*f*f

    exact = (
        (F(1800,61) / (4*F(7,6))) == F(2700,427) < F(13,2),
        (discount,slope,shared) == (F(24,49),F(25,84),F(191,441)),
        (end,upper) == (F(24,35),F(288,175)),
        F(1,5) < end < upper,
        envelope(F(1,5)) < 1,
        envelope(end) < 1,
        shared*upper < 1,
    )
    if not all(exact):
        raise ArithmeticError("The large-fourth-gap proof constants failed")
    print(f"Verified all {len(exact)} large-fourth-gap rational bounds.")


if __name__ == "__main__":
    main()

