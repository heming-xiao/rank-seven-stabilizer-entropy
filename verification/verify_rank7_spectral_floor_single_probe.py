"""Verify the uniform eleven floor prices for every sorted rank-seven spectrum."""

from fractions import Fraction as F
from math import prod
import json
from pathlib import Path

from verify_rank7_forward_coefficients import (
    CAP_01, CAP_02, EXCEPTION_DUALS, KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE,
    coefficient_table, row_table, verify_dual,
)


# Each integer is four times its physical row's dual price.
FLOOR_ROWS = {
    "0666": (F(1, 2), {12: 2, 18: 2, 24: 2, 30: 2, 36: 2}),
    "1666": (1, {12: 2, 13: 2, 18: 2, 19: 2, 24: 2, 25: 2, 30: 2, 31: 2, 36: 2, 37: 2}),
    "2666": (F(3, 2), {1: 4, 13: 2, 18: 4, 19: 2, 24: 4, 25: 2, 30: 4, 31: 2, 36: 4, 37: 2}),
    "3666": (2, {18: 2, 19: 2, 24: 2, 25: 2, 28: 2, 29: 2, 30: 4, 31: 4, 33: 2, 35: 2,
                 36: 4, 37: 4, 39: 2, 41: 2, 77: 4, 88: 2, 89: 2}),
    "4666": (4, {12: 4, 13: 4, 18: 4, 19: 4, 24: 4, 25: 4, 30: 8, 31: 4, 36: 5,
                 37: 5, 38: 1, 39: 1, 40: 1, 41: 1, 77: 8, 81: 4}),
    "5666": (6, {12: 4, 13: 4, 24: 4, 25: 4, 30: 8, 31: 8, 36: 8, 37: 8, 41: 4,
                 77: 12, 88: 8, 89: 4, 92: 8, 93: 4, 94: 4}),
    "6666": (2, {18: 2, 19: 2, 24: 2, 25: 2, 30: 2, 31: 2, 77: 4, 88: 2, 89: 2,
                 90: 2, 91: 4, 94: 2, 96: 2, 97: 2}),
    "0466": (F(1, 2), {12: 2, 18: 2, 24: 2, 30: 6, 36: 6}),
    "0566": (1, {12: 4, 18: 4, 24: 4, 30: 4, 36: 8}),
    "1466": (1, {12: 2, 13: 2, 18: 2, 19: 2, 24: 2, 25: 2, 30: 6, 31: 6, 36: 6, 37: 6}),
    "1566": (2, {12: 4, 13: 4, 18: 4, 19: 4, 24: 4, 25: 4, 30: 4, 31: 4, 36: 8, 37: 8}),
}


def verify_prices():
    source = (Path(__file__).resolve().parents[1] / "certificates" / "rank7" / "rank7_forward_coefficients.json")
    records = json.loads(source.read_text(encoding="utf-8"))["old_certificates"]
    old = {tuple(record["monomial"]): record["prices"] for record in records}
    wedges = [UNIVERSE.difference(triple) for triple in TRIPLES]
    first = [int({0, 1} <= wedge) for wedge in wedges]
    second = [int({0, 2} <= wedge) for wedge in wedges]
    matrix = row_table()[:len(KNOWN_ROWS)]
    capacities = [row[2] for row in KNOWN_ROWS]
    for monomial, costs in coefficient_table().items():
        name = "".join(map(str, monomial))
        if name in FLOOR_ROWS:
            charge, multipliers = FLOOR_ROWS[name]
            prices = [(i, F(value, 4)) for i, value in multipliers.items()]
            adjusted = [value + charge * x for value, x in zip(costs, first)]
        elif monomial in EXCEPTION_DUALS:
            rows = EXCEPTION_DUALS[monomial]
            prices = [(KNOWN_ROWS.index(row), 1) for row in rows if row in KNOWN_ROWS]
            adjusted = [value - rows.count(CAP_01)*x - rows.count(CAP_02)*y
                        for value, x, y in zip(costs, first, second)]
        else:
            prices = old[monomial]
            adjusted = costs
        reference = sum(value for value, triple in zip(adjusted, TRIPLES) if triple in REFERENCE)
        if verify_dual(prices, matrix, capacities, adjusted) != reference:
            raise ArithmeticError(f"Incorrect reference value for {name}")
    print("Verified physical row prices for all 210 quartic monomials (7350 columns).")


def verify_spectrum():
    alpha, beta, gamma, a, b, c, d = map(F, ("7.9", "3.8", "1.7", "1.4", "1.3", "1.1", "1"))
    h, k, q = alpha-beta, beta-gamma, gamma-a
    g, delta = h*q, k*(alpha-a)
    gaps = (h, k, q, a-b, b-c, c-d, d)
    charges = sum(rho*prod(gaps[int(i)] for i in key) for key, (rho, _) in FLOOR_ROWS.items())
    floor = d**2*(delta-(h/2+k)*(b+c-d)-d*(3*q/2+2*(a+b+c-2*d)))
    head = g-b*(h+3*q)-5*b*b/2
    reserve = k*k*(k*k+(h*h+q*q)/2)
    theta = F(1, 7)
    net = (1-theta)*floor-theta*k*b*c*d
    margin = (12*delta**2+reserve)/F(5, 2)-168*net
    if not (delta*d*d-charges == floor == F(379,100)
            and g/(g-head) == F(82,715) < theta
            and net == F(19737,7000) and margin == F(5541813,12500)):
        raise ArithmeticError("Rational spectrum check failed")
    print(f"At the residual spectrum the strict margin per positive excess is {margin}.")


if __name__ == "__main__":
    verify_prices()
    verify_spectrum()
