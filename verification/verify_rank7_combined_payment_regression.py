"""Exact regression array for testing joint mixed and compression certificates."""

from fractions import Fraction as F
from itertools import combinations
from math import prod

from verify_rank7_forward_coefficients import KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE, row_table


SPECTRUM = tuple(map(F, ("19.32", "4.69", "4.13", "1.012", "1.008", "1.004", "1")))
WEIGHTS_IN_THIRDS = {
    "0123": 1, "0124": 2, "0135": 1, "0136": 1, "0145": 1, "0156": 1,
    "0235": 1, "0236": 1, "0246": 1, "0456": 1, "1256": 2, "1346": 2,
    "2345": 2, "2346": 1,
}


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def main():
    wedges = [UNIVERSE.difference(triple) for triple in TRIPLES]
    weights = [F(WEIGHTS_IN_THIRDS.get("".join(map(str, sorted(wedge))), 0), 3)
               for wedge in wedges]
    for row, (_, _, cap) in zip(row_table()[:len(KNOWN_ROWS)], KNOWN_ROWS, strict=True):
        require(sum(a * b for a, b in zip(row, weights, strict=True)) <= cap,
                "An original packing row is violated")
    for pair in combinations(range(7), 2):
        require(sum(weight for weight, wedge in zip(weights, wedges, strict=True)
                    if set(pair) <= wedge) <= F(7, 3), "A five-set cap is violated")

    differences = [weight - int(triple in REFERENCE)
                   for weight, triple in zip(weights, TRIPLES, strict=True)]

    def pair_differences(pair):
        unweighted = F(0)
        weighted = F(0)
        for difference, wedge in zip(differences, wedges, strict=True):
            if pair <= wedge:
                unweighted += difference
                weighted += difference * prod(SPECTRUM[i] for i in wedge - pair)
        return unweighted, weighted

    v, u1 = pair_differences({0, 1})
    v2, u2 = pair_differences({0, 2})
    nu, u = v + v2, u1 + u2
    scores = [prod(SPECTRUM[i] for i in wedge) for wedge in wedges]
    gain = sum(w * cost for w, cost in zip(differences, scores, strict=True))
    require((v, nu, u1, u, gain) == (
        F(1, 3), F(1, 3), F(30467, 93750), F(29671, 93750), F(40180968947, 4687500000)
    ), "Unexpected weighted differences")

    alpha, beta, gamma, a, b, c, d = SPECTRUM
    h, k, q = alpha - beta, beta - gamma, gamma - a
    g, delta = h * q, k * (alpha - a)
    r = k**2 * (k**2 + (h**2 + q**2) / 2)
    # Abstract Gram variables with zero cross coefficient, stronger individual
    # geometry and no negative tail price.
    kappa, kappa1 = nu / 12, 20 * v / 49
    best_mixed = (12 * (u + g * kappa)**2 / kappa
                  + 12 * (u1 + delta * kappa1)**2 / kappa1)
    reduced_gap = 168 * gain - best_mixed - g**2 * kappa - r * kappa1
    require(reduced_gap == F(373770063497671, 11250000000000),
            "The reduced two-probe obstruction changed")

    s = max(F(0), g - F(200, 11) * b * (c - d))
    fixed_payment = (24 * delta * u1 + 24 * s * u
                     + (12 * delta**2 + r) * F(2, 5) * v
                     + (12 * s**2 + g**2) * nu / 12)
    unpaid = 168 * gain - fixed_payment
    threshold = F(50069229, 625000)
    require(threshold in scores, "Missing compression threshold")
    previous = max(value for value in scores if value < threshold)
    trace = sum(weight for value, weight in zip(scores, weights, strict=True)
                if value >= threshold)
    require(trace == F(10, 3), "Unexpected nested trace")
    compression_payment = 96 * F(2, 9) * (threshold - previous)**2 / (2 * (threshold + previous))
    require(92 < unpaid < 93 and compression_payment > 388, "Joint payment failed")
    print(f"119 rows checked; optimized mixed-only reduced gap: {reduced_gap}.")
    print(f"Actual uniform shifts leave {float(unpaid):.6f}; one compression layer pays >388.")


if __name__ == "__main__":
    main()
