"""Exact fixed-frame split-loss certificate. Run with Python's standard library."""
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
import json
from pathlib import Path

from verify_rank7_forward_coefficients import (
    KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE, coefficient_table, row_table, verify_dual
)


TAIL = (3, 4, 5, 6)
WEDGES = [UNIVERSE.difference(t) for t in TRIPLES]
REFERENCE_COLUMNS = [i for i, triple in enumerate(TRIPLES) if triple in REFERENCE]
ROWS = {row: i for i, row in enumerate(KNOWN_ROWS)}


def product_coefficient(labels, monomial):
    """Coefficient in a product of probabilities, in the seven forward gaps."""
    return sum(tuple(sorted(term)) == monomial
               for term in product(*(range(label, 7) for label in labels)))


def shared_completion_charge(wedge, monomial):
    """Coefficient of q(q + 3a - b - c - d) times the weighted completion."""
    heads = {0, 1, 2}
    if not heads <= wedge:
        return 0
    tail, = wedge - heads
    return sum(price for slot, price in ((2, 1), (3, 3), (4, 2), (5, 1))
               for last in range(tail, 7) if tuple(sorted((2, slot, last))) == monomial)


def pair_dual(tail_monomial):
    """Weighted six-pair proof. Edge ij is charged to the row missing the other two tails."""
    prices = []
    for edge in combinations(TAIL, 2):
        price = product_coefficient(edge, tail_monomial)
        if price:
            missing = tuple(sorted(set(TAIL).difference(edge)))
            prices.append((ROWS["pair", missing, 1], price))
    return prices


def additional_floor_duals():
    """Five q-free rows spend the coefficient of b*c*d on the excess L01 - 2."""
    def symmetric_directed(prices):
        return {ROWS["directed_link", (i, head), 2]: Fraction(price)
                for i, price in prices.items() for head in (0, 1)}

    half = Fraction(1, 2)
    first = symmetric_directed({2: half, 3: half, 5: 3*half, 6: 7*half})
    for i, j, price in ((2,4,half), (3,4,half), (4,5,half), (4,6,half), (5,6,2)):
        first[ROWS["pair", (i,j), 1]] = price
    return {
        (4,5,6): first,
        (4,6,6): symmetric_directed({2: half, 3: half, 4: half, 5: 3*half, 6: 3*half}),
        (5,5,6): symmetric_directed({2: half, 3: half, 4: half, 5: half, 6: 5*half}),
        (5,6,6): symmetric_directed({2: 1, 3: 1, 4: 1, 5: 1, 6: 2}),
        (6,6,6): symmetric_directed({2: half, 3: half, 4: half, 5: half, 6: half}),
    }


def verify_physical_swap(table):
    """Interchanging labels 5 and 6 gives E = -k(h+k+q)*b*(c-d)."""
    permutation = (0, 1, 2, 3, 4, 6, 5)
    swapped = {tuple(sorted(permutation[label] for label in triple)) for triple in REFERENCE}
    swapped_columns = [i for i, triple in enumerate(TRIPLES) if triple in swapped]
    expected = {}
    for leading_gap in (0, 1, 2):
        for tail_gap in (4, 5, 6):
            monomial = tuple(sorted((1, leading_gap, tail_gap, 5)))
            expected[monomial] = expected.get(monomial, 0) - 1
    for monomial, costs in table.items():
        discrepancy = sum(costs[i] for i in swapped_columns) - sum(costs[i] for i in REFERENCE_COLUMNS)
        if discrepancy != expected.get(monomial, 0):
            raise ArithmeticError(f"Incorrect physical-swap identity for {monomial}")


def main():
    source = (Path(__file__).resolve().parents[1] / "certificates" / "rank7" / "rank7_forward_coefficients.json")
    baseline = {tuple(record["monomial"]): record["prices"]
                for record in json.loads(source.read_text(encoding="utf-8"))["old_certificates"]}
    table = coefficient_table()
    matrix = row_table()[:len(KNOWN_ROWS)]
    capacities = [row[2] for row in KNOWN_ROWS]
    highest = [int({0, 1} <= wedge) for wedge in WEDGES]
    floor_duals = additional_floor_duals()
    counts = {"six_pair": 0, "ordinary": 0, "additional": 0}
    for monomial in combinations_with_replacement(range(2, 7), 3):
        quartic = (1, *monomial)
        costs = table[quartic].copy()
        if monomial[0] == 2:
            tail_monomial = monomial[1:]
            for i, wedge in enumerate(WEDGES):
                if highest[i]:
                    costs[i] -= product_coefficient(tuple(wedge - {0, 1}), tail_monomial)
                costs[i] -= shared_completion_charge(wedge, monomial)
            prices = pair_dual(tail_monomial)
            counts["six_pair"] += 1
        elif monomial in floor_duals:
            slope = product_coefficient((4,5,6), monomial)
            costs = [cost + slope*pair for cost, pair in zip(costs, highest)]
            prices = list(floor_duals[monomial].items())
            counts["additional"] += 1
        else:
            if product_coefficient((4,5,6), monomial):
                raise ArithmeticError(f"Missing floor certificate for {monomial}")
            prices = baseline[quartic]
            counts["ordinary"] += 1
        reference_value = sum(costs[i] for i in REFERENCE_COLUMNS)
        if verify_dual(prices, matrix, capacities, costs) != reference_value:
            raise ArithmeticError(f"Reference mismatch for {monomial}")
    if counts != {"six_pair": 15, "ordinary": 15, "additional": 5}:
        raise ArithmeticError(f"Missing coefficients: {counts}")
    verify_physical_swap(table)
    print("35 cubic coefficients and 1225 column inequalities verified exactly.")
    print("Six physical pair rows certify all 15 coefficients involving q.")
    print("Five q-free duals retain the additional b*c*d*(L01 - 2) charge.")
    print("The physical 5/6 swap attains equality on all 210 quartic coefficients.")


if __name__ == "__main__":
    main()

