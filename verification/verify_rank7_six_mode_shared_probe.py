"""Verify the matching costs in the rank-seven shared and triangle bounds."""

from fractions import Fraction as F
from functools import reduce
from itertools import combinations, product
from operator import xor

from verify_rank6_two_probe_endpoint import matchings
from verify_rank7_four_equal_tails import multiply, sum_polynomials


def verify_shared_bound():
    vertices = tuple(range(6))
    heads = ({0, 1}, {0, 2})
    prices = {
        edge: sum(head <= set(vertices).difference(edge) for head in heads)
        for edge in combinations(vertices, 2)
    }
    all_matchings = matchings(vertices)
    if len(all_matchings) != 76:
        raise ArithmeticError("Missing six-mode matchings")
    reference = ((0, 1), (2, 3), (4, 5))
    if sum(prices[edge] for edge in reference) != 3:
        raise ArithmeticError("Six-mode reference must reach three")
    if any(sum(prices[edge] for edge in matching) > 3 for matching in all_matchings):
        raise ArithmeticError("Six-mode shared price exceeds three")
    return len(all_matchings)


def verify_triangle_bound():
    vertices = tuple(range(7))
    leading = tuple(combinations(range(3), 2))
    probabilities = [{(j,): 1 for j in vertices[i:]} for i in vertices]
    baseline = [probabilities[max(i, 3)] for i in vertices]
    increments = [
        sum_polynomials((1, probabilities[i]), (-1, baseline[i]))
        for i in range(3)
    ]
    prices = {
        (i, j): sum_polynomials(
            (1, multiply(probabilities[i], probabilities[j])),
            (-1, multiply(baseline[i], baseline[j])),
        )
        for i, j in combinations(vertices, 2)
    }

    completion = multiply(
        probabilities[3], sum_polynomials(*[(1, inc) for inc in increments]),
    )
    bounds = {
        (i, j): sum_polynomials((1, completion), (1, multiply(increments[i], increments[j])))
        for i, j in leading
    }
    bounds[None] = sum_polynomials(*[
        (1, multiply(inc, probabilities[i + 3])) for i, inc in enumerate(increments)
    ])
    references = {
        (0, 1): ((0, 1), (2, 3), (4, 5)),
        (0, 2): ((0, 2), (1, 3), (4, 6)),
        (1, 2): ((1, 2), (0, 3), (5, 6)),
        None: ((0, 3), (1, 4), (2, 5)),
    }
    all_matchings = matchings(vertices)
    if len(all_matchings) != 232:
        raise ArithmeticError("Missing seven-mode matchings")
    for matching in all_matchings:
        mode = next((edge for edge in matching if edge in leading), None)
        loss = sum_polynomials((1, bounds[mode]), *[(-1, prices[edge]) for edge in matching])
        if any(value < 0 for value in loss.values()):
            raise ArithmeticError(f"Negative coefficient for {matching}")
        if matching == references[mode] and any(loss.values()):
            raise ArithmeticError(f"Reference fails to saturate {mode}")
    return len(all_matchings)


def verify_physical_witness():
    supports = ((0, 2), (1, 4), (8,), (0, 2), (1, 4))

    def direction_weights(i, j):
        pairs = tuple(product(supports[i], supports[j]))
        directions = {x ^ y: F(1, len(pairs)) for x, y in pairs}
        if len(directions) != len(pairs):
            raise ArithmeticError("A skew direction has several contributing support pairs")
        return directions

    shared = {}
    for i, j in combinations(range(3), 2):
        for direction, weight in direction_weights(i, j).items():
            shared[direction] = shared.get(direction, 0) + weight
        for coordinates in product(*(supports[k] for k in (i, j, 3, 4))):
            if len(set(coordinates)) == 4 and reduce(xor, coordinates) == 0:
                raise ArithmeticError("The witness's wedge contains a zero-XOR quadruple")
    cross = -sum(shared.get(direction, 0) * weight
                 for direction, weight in direction_weights(3, 4).items())
    triangle = sum(weight * (1 - weight) for weight in shared.values())
    if cross != -F(1, 4) or triangle != F(7, 4):
        raise ArithmeticError("Incorrect physical cross polarization or triangle defect")


def main():
    six = verify_shared_bound()
    seven = verify_triangle_bound()
    g, tail_price, weight = 50, 3, F(133, 6)
    if not (g - F(200, 11) * tail_price < 0
            and g / (1 + 12 * tail_price**2 / weight) == F(6650, 781)):
        raise ArithmeticError("Invalid example for the shared shift")
    verify_physical_witness()
    print(f"Verified {six} six-mode and {seven} seven-mode matchings, the shift and the physical witness.")


if __name__ == "__main__":
    main()

