"""Certify additional forward-coefficient losses for (1,r,r,a,b,c,c)."""

from fractions import Fraction

from verify_rank7_forward_coefficients import (
    KNOWN_ROWS,
    REFERENCE,
    TRIPLES,
    UNIVERSE,
    coefficient_table,
    row_table,
)


def sparse_dual(directed=(), pairs=(), four_sets=()):
    prices = {}
    for kind, capacity, entries in (
        ("directed_link", 2, directed),
        ("pair", 1, pairs),
        ("four_set", 1, four_sets),
    ):
        for labels, price in entries:
            row = kind, tuple(map(int, labels)), capacity
            prices[row] = Fraction(price)
    return prices


CERTIFICATES = {
    (0, 4, 6, 6): (1, sparse_dual(directed=[("30", 1), ("40", 1), ("50", 2), ("60", 2)])),
    (2, 4, 6, 6): (3, sparse_dual(
        directed=[("12", 1), ("21", 1), ("30", 1), ("40", 1), ("50", 2), ("60", 2), ("61", 1), ("62", 1)],
        pairs=[("05", 1), ("34", 2), ("35", 3), ("36", 2), ("45", 3), ("46", 2), ("56", 3)],
    )),
    (3, 4, 6, 6): (4, sparse_dual(
        directed=[("03", 1), ("12", 1), ("21", 1), ("30", 1), ("40", 2), ("50", 4), ("51", 2), ("52", 2), ("60", 4), ("61", 2), ("62", 2)],
        pairs=[("34", 2), ("45", 1), ("46", 1)],
    )),
    (3, 6, 6, 6): (4, sparse_dual(
        directed=[("03", 1), ("12", 1), ("21", 1), ("30", 1), ("40", 2), ("50", 2), ("60", 2)],
        pairs=[("34", 2), ("35", 2), ("36", 2), ("45", 2), ("46", 2), ("56", 2)],
    )),
    (4, 4, 6, 6): (Fraction(5, 2), sparse_dual(
        directed=[("12", "1/2"), ("21", "1/2"), ("30", 1), ("40", 1), ("50", "7/3"), ("51", "4/3"), ("52", "4/3"), ("53", "1/3"), ("54", "1/3"), ("60", "13/6"), ("61", "7/6"), ("62", "7/6"), ("63", "1/6"), ("64", "1/6"), ("65", "1/2")],
        pairs=[("01", "1/2"), ("02", "1/2"), ("34", 1)],
    )),
    (4, 6, 6, 6): (5, sparse_dual(
        directed=[("12", 1), ("21", 1), ("30", 2), ("40", 2), ("50", 3), ("51", 1), ("52", 1), ("60", 3), ("61", 1), ("62", 1)],
        pairs=[("01", 1), ("02", 1), ("34", 2), ("35", 1), ("36", 1), ("45", 1), ("46", 1)],
    )),
    (2, 2, 3, 6): (1, sparse_dual(
        directed=[("30", 1)], pairs=[("45", 2), ("46", 2), ("56", 2)], four_sets=[("3456", 2)],
    )),
    (0, 2, 3, 3): (2, sparse_dual(
        directed=[("30", 2)], pairs=[("45", 2), ("46", 2), ("56", 2)],
    )),
    (0, 2, 3, 4): (2, sparse_dual(
        directed=[("30", 2)], pairs=[("45", 2), ("46", 2), ("56", 3)], four_sets=[("3456", 1)],
    )),
}


def main():
    physical_rows = dict(zip(KNOWN_ROWS, row_table()))
    costs = coefficient_table()
    shared_pair_counts = [
        int({0, 1} <= UNIVERSE.difference(triple))
        + int({0, 2} <= UNIVERSE.difference(triple))
        for triple in TRIPLES
    ]
    for monomial, (slope, prices) in CERTIFICATES.items():
        objective = [
            coefficient + slope * pair_count
            for coefficient, pair_count in zip(costs[monomial], shared_pair_counts)
        ]
        if any(price < 0 or row not in physical_rows for row, price in prices.items()):
            raise ArithmeticError(f"Invalid physical row in {monomial}")
        for column, target in enumerate(objective):
            dual_coefficient = sum(price * physical_rows[row][column] for row, price in prices.items())
            if dual_coefficient < target:
                raise ArithmeticError(f"Unproved coefficient for {monomial} at {TRIPLES[column]}")
        dual_value = sum(price * row[2] for row, price in prices.items())
        reference_value = sum(coefficient for coefficient, triple in zip(objective, TRIPLES) if triple in REFERENCE)
        if dual_value != reference_value:
            raise ArithmeticError(f"Incorrect reference cost for {monomial}: {dual_value} != {reference_value}")
        print(f"{monomial}: coefficient deficit >= {slope} * nu")


if __name__ == "__main__":
    main()
