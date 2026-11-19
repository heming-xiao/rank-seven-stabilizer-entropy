"""Check a strictly ordered rank-seven packing relaxation witness exactly."""

from fractions import Fraction as F
from itertools import combinations
from math import prod

from verify_rank7_forward_coefficients import KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE, row_table


WEDGE_WEIGHTS_IN_SIXTHS = {
    "0123": 4, "0124": 2, "0135": 2, "0145": 2, "0146": 2, "0156": 2,
    "0236": 1, "0245": 2, "0246": 1, "0256": 1, "0346": 2, "0356": 2,
    "1236": 1, "1246": 1, "1256": 3, "1345": 2, "1346": 2, "2345": 4,
    "2346": 2,
}


def main():
    wedges = [UNIVERSE.difference(triple) for triple in TRIPLES]
    weights = [
        F(WEDGE_WEIGHTS_IN_SIXTHS.get("".join(map(str, sorted(wedge))), 0), 6)
        for wedge in wedges
    ]
    for row, (_, _, capacity) in zip(row_table()[:len(KNOWN_ROWS)], KNOWN_ROWS, strict=True):
        if sum(weight * value for weight, value in zip(weights, row, strict=True)) > capacity:
            raise ArithmeticError("Packing witness violates a physical row")
    pair_occupancies = {
        pair: sum(weight for weight, wedge in zip(weights, wedges) if set(pair) <= wedge)
        for pair in combinations(range(7), 2)
    }
    if max(pair_occupancies.values()) > F(7, 3):
        raise ArithmeticError("Packing witness violates the five-set upper bound")

    spectrum = tuple(map(F, ("79/10", "19/5", "17/10", "7/5", "13/10", "11/10", "1")))
    scores = [prod(spectrum[label] for label in wedge) for wedge in wedges]
    reference = sum(score for triple, score in zip(TRIPLES, scores) if triple in REFERENCE)
    gain = sum(weight * score for weight, score in zip(weights, scores)) - reference
    if gain != F(12373, 30000):
        raise ArithmeticError(f"Unexpected gain: {gain}")

    alpha, beta, gamma, a, b, c, d = spectrum
    h = alpha - beta
    k = beta - gamma
    q = gamma - a
    g = h * q
    delta = k * (alpha - a)
    eta = k**2 * (k**2 + (h**2 + q**2) / 2)
    highest_squared = alpha * beta * c * d
    next_squared = alpha * gamma * a * b
    compression_upper = 16 * (highest_squared - next_squared)**2 / next_squared
    bound = (12 * delta**2 + eta) / F(5, 2) + max(g**2 / 24, q**4 / 72) + 30 * d**4
    coefficient = 144 * d**2 * delta - 168 * k * b * c * d
    criterion_gap_lower = coefficient - bound - compression_upper
    if not (
        delta >= F(5, 2) * d**2
        and highest_squared > next_squared
        and alpha - a > F(7, 5) * (b + c - d)
        and alpha > 3 * b
        and 1 / a > 1 / alpha + 1 / beta
        and criterion_gap_lower == F(288248021163, 618800000)
    ):
        raise ArithmeticError("The spectrum is not in the stated residual region")
    print(f"119 physical packing rows checked; normalized relaxed gain: {gain}")
    print(f"Highest pair occupancy: {pair_occupancies[0, 1]}; criterion gap > {criterion_gap_lower}")


if __name__ == "__main__":
    main()
