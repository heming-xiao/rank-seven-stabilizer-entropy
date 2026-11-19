"""Exact constants for the analytic separated-bottom-pair comparison."""

from fractions import Fraction as F


def main():
    j = F(122, 25)
    center = 72/j
    peak = j*center**2
    greatest_d, least_b = F(9,25), F(189,50)
    k_limit, q_floor = F(13,50), F(151,100)
    checks = {
        "highest quadratic scales": 24*peak < 160**2 and 72*peak < 17**4,
        "base spectral threshold": F(9,5)*(2-F(9,5)) == greatest_d
                                   and F(7,6)*F(9,5)**2 == least_b,
        "split bound": 2*center*greatest_d**2/(4*least_b) < k_limit,
        "low-head lower bound": F(9,5)-2*k_limit/F(9,5) > q_floor,
        "low-X branch": 17**2*(greatest_d-least_b/12) < 4**2
                        and least_b/greatest_d-k_limit > 4+q_floor,
        "high-X branch": F(51,5)**2 == 17**2*greatest_d
                          and 12-k_limit > F(51,5)+q_floor,
        "final square": 4*160*q_floor*least_b
                        > (160*greatest_d+q_floor*(k_limit+q_floor))**2,
        "large fifth split": 2*center/(4*F(7,6)) < F(13,2),
        "large fifth head bound": 9**2 > 39 and 2*9 > 17,
        "large fifth AM-GM scale": F(223,10)**2 < 4*160*F(2,3)*F(7,6),
        "large fifth concavity endpoints": all(
            F(223,10)*b > 160+F(13,3)+F(4,9)*b*b for b in (9,21)
        ),
    }
    for name, checked in checks.items():
        if not checked:
            raise ArithmeticError(f"Invalid separated-bottom constant: {name}")
    print(f"Verified {len(checks)} separated-bottom analytic inequalities exactly.")


if __name__ == "__main__":
    main()

