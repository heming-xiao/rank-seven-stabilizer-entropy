"""Exact rank-seven packing certificate for the previous strictly ordered residual."""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import prod

from verify_rank7_forward_coefficients import KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE, row_table


CENTER = tuple(map(F, ("79/10", "19/5", "17/10", "7/5", "13/10", "11/10", "1")))
RADIUS = F(1, 5000)
FIXED_PRICES = {
    ("directed_link", (2, 0), 2): 703,
    ("directed_link", (2, 1), 2): 417,
    ("directed_link", (3, 0), 2): 1203,
    ("directed_link", (3, 1), 2): 674,
    ("directed_link", (4, 0), 2): 1282,
    ("directed_link", (4, 1), 2): 515,
    ("directed_link", (5, 0), 2): 1725,
    ("directed_link", (5, 1), 2): 740,
    ("directed_link", (6, 0), 2): 1098,
    ("directed_link", (6, 3), 2): 49,
    ("four_set", (0, 1, 5, 6), 1): 111,
    ("four_set", (2, 3, 4, 6), 1): 124,
    ("four_set", (2, 3, 5, 6), 1): 432,
    ("four_set", (2, 4, 5, 6), 1): 732,
    ("four_set", (3, 4, 5, 6), 1): 1683,
    ("pair", (0, 1), 1): 406,
    ("pair", (2, 6), 1): 811,
    ("pair", (3, 6), 1): 1054,
    ("pair", (4, 5), 1): 267,
    ("pair", (4, 6), 1): 1334,
    ("pair", (5, 6), 1): 1724,
}


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def add_scaled(target, source, scalar):
    for monomial, coefficient in source.items():
        target[monomial] += scalar * coefficient


def multiply(*factors):
    result = {(): F(1)}
    for factor in factors:
        expanded = Counter()
        for (left, x), (right, y) in product(result.items(), factor.items()):
            expanded[tuple(sorted(left + right))] += x * y
        result = expanded
    return result


def centered_costs():
    # Work on the slice t_6=1. The other probabilities are CENTER[i]+x_i.
    t = [{(): value, (i,): F(1)} for i, value in enumerate(CENTER[:-1])]
    t.append({(): CENTER[-1]})

    def gap(i, j):
        polynomial = Counter(t[i])
        add_scaled(polynomial, t[j], -1)
        return polynomial

    h, k, q = gap(0, 1), gap(1, 2), gap(2, 3)
    delta = multiply(k, gap(0, 3))
    rate = multiply(delta, delta)
    for monomial in rate:
        rate[monomial] *= F(12, 5)
    add_scaled(rate, multiply(k, k, k, k), F(1, 5))
    add_scaled(rate, multiply(k, k, h, h), F(1, 10))
    add_scaled(rate, multiply(k, k, q, q), F(1, 10))

    costs = []
    for triple in TRIPLES:
        wedge = UNIVERSE.difference(triple)
        cost = Counter()
        add_scaled(cost, multiply(*(t[i] for i in sorted(wedge))), 168)
        if {0, 1} <= wedge:
            add_scaled(cost, multiply(delta, *(t[i] for i in sorted(wedge - {0, 1}))), -12)
            add_scaled(cost, rate, -1)
        costs.append(cost)
    return costs


def lower_bound(polynomial, radius):
    return polynomial[()] - sum(abs(c) * radius**len(m) for m, c in polynomial.items() if m)


def verify(radius):
    require(radius >= 0 and 2 * radius < min(
        left - right for left, right in zip(CENTER, CENTER[1:])
    ), "Box must preserve strict order")
    costs = centered_costs()
    rows = dict(zip(KNOWN_ROWS, row_table()[:len(KNOWN_ROWS)], strict=True))
    reference = [i for i, triple in enumerate(TRIPLES) if triple in REFERENCE]
    budget = [F(0)] * len(TRIPLES)
    for row, price in FIXED_PRICES.items():
        require(price > 0, f"Nonpositive fixed price: {row}")
        require(sum(rows[row][i] for i in reference) == row[2], f"Row is slack: {row}")
        for i, coefficient in enumerate(rows[row]):
            budget[i] += price * coefficient

    dual = [Counter({(): value}) for value in budget]
    variable_prices = []
    for i in reference:
        row = next(row for row in KNOWN_ROWS if row[0] == "four_set" and rows[row][i])
        require(row not in FIXED_PRICES and sum(rows[row][j] for j in reference) == 1,
                f"Invalid variable price row: {row}")
        price = Counter(costs[i])
        price[()] -= budget[i]
        variable_prices.append(lower_bound(price, radius))
        for j, coefficient in enumerate(rows[row]):
            add_scaled(dual[j], price, coefficient)
    require(min(variable_prices) > 0, "A variable price may be nonpositive in the box")

    off_reference = []
    for i, (amount, cost) in enumerate(zip(dual, costs, strict=True)):
        add_scaled(amount, cost, -1)
        if i in reference:
            require(not any(amount.values()), f"Reference equality failed: {TRIPLES[i]}")
        else:
            off_reference.append(lower_bound(amount, radius))
    require(min(off_reference) > 0, "A nonreference column may be uncovered in the box")
    return min(variable_prices), min(off_reference)


def main():
    price, slack = verify(RADIUS)
    print(f"Seven reference equalities and 28 strict column inequalities hold at radius {RADIUS}.")
    print(f"Minimum variable price >= {price}; minimum off-reference slack >= {slack}.")


if __name__ == "__main__":
    main()
