"""Check simultaneous rank-six endpoint prices in exact forward gaps."""

from collections import defaultdict
from fractions import Fraction
from functools import cache, reduce
from itertools import combinations
from operator import xor


LABELS = tuple(range(6))
ZERO = (0,) * len(LABELS)


def sum_polynomials(terms):
    result = defaultdict(Fraction)
    for polynomial, factor in terms:
        for monomial, coefficient in polynomial.items():
            result[monomial] += factor * coefficient
    return {monomial: coefficient for monomial, coefficient in result.items() if coefficient}


def multiply(left, right):
    result = defaultdict(Fraction)
    for first, a in left.items():
        for second, b in right.items():
            result[tuple(i + j for i, j in zip(first, second))] += a * b
    return dict(result)


def gap(index):
    return {tuple(int(i == index) for i in LABELS): Fraction(1)}


def product_probabilities(labels):
    result = {ZERO: Fraction(1)}
    for label in labels:
        value = sum_polynomials((gap(index), 1) for index in LABELS if index >= label)
        result = multiply(result, value)
    return result


@cache
def matchings(vertices):
    if not vertices:
        return ((),)
    first, *rest = vertices
    result = list(matchings(tuple(rest)))
    for position, partner in enumerate(rest):
        remaining = tuple(rest[:position] + rest[position + 1:])
        result.extend(((first, partner),) + suffix for suffix in matchings(remaining))
    return tuple(result)


def main():
    weights = {}
    reference = []
    for edge in combinations(LABELS, 2):
        wedge = set(LABELS).difference(edge)
        exterior = product_probabilities(wedge)
        first_probe = product_probabilities(wedge - {0, 1}) if {0, 1} <= wedge else {}
        second_probe = product_probabilities(wedge - {0, 2}) if {0, 2} <= wedge else {}
        shared = sum_polynomials(((first_probe, 1), (second_probe, 1)))
        weights[edge] = exterior, shared, first_probe
        if reduce(xor, wedge) == 0:
            reference.append(edge)

    assert set(reference) == {(4, 5), (2, 3), (0, 1)}
    shared_price = multiply(gap(0), gap(2))
    highest_price = multiply(gap(1), sum_polynomials((gap(i), 1) for i in range(3)))
    all_matchings = matchings(LABELS)
    assert len(all_matchings) == 76
    for matching in all_matchings:
        losses = []
        for component in range(3):
            loss = sum_polynomials(
                [(weights[edge][component], 1) for edge in reference]
                + [(weights[edge][component], -1) for edge in matching]
            )
            losses.append(loss)
        exterior_loss, shared_loss, highest_loss = losses
        adjusted = sum_polynomials((
            (exterior_loss, 2),
            (multiply(shared_price, shared_loss), -1),
            (multiply(highest_price, highest_loss), -1),
        ))
        for label, polynomial in (
            ("shared loss", shared_loss), ("highest loss", highest_loss),
            ("adjusted exterior loss", adjusted),
        ):
            if any(value < 0 for value in polynomial.values()):
                raise ArithmeticError(f"Negative coefficient in {label} for {matching}")
    print("Rank-six endpoint: 76 matchings, 228 exact coefficient comparisons")


if __name__ == "__main__":
    main()
