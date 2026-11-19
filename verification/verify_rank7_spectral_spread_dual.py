"""Independently verify the rank-7 ratio-at-most-three packing certificates."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from math import prod
from pathlib import Path

from verify_rank7_fano_dual import MONOMIALS, PAIRS, TRIPLES, VERTICES, require


def scaled_cubic_coefficients(triple):
    """Expand the three factors 2a_i by sparse polynomial multiplication."""
    polynomial = {(): 1}
    for vertex in triple:
        factor = [2] + [1 + 2 * int(variable <= vertex) for variable in range(1, 7)]
        next_polynomial = Counter()
        for monomial, coefficient in polynomial.items():
            for variable, multiplier in enumerate(factor):
                next_monomial = tuple(sorted((*monomial, variable)))
                next_polynomial[next_monomial] += coefficient * multiplier
        polynomial = next_polynomial
    require(set(polynomial) == MONOMIALS,
            f"Incorrect expansion support for triple {triple}")
    require(sum(polynomial.values()) == prod(8 + 2 * vertex for vertex in triple),
            f"Incorrect expansion mass for triple {triple}")
    return polynomial


def verify(data):
    require(Fraction(data["maximum_ratio_of_largest_to_smallest_probability"]) == 3,
            "Unexpected spectral ratio")
    require(tuple(data["vertex_labels"]) == VERTICES, "Unexpected vertex labels")
    pair_order = tuple(map(tuple, data["pair_order"]))
    require(len(pair_order) == len(PAIRS) and set(pair_order) == set(PAIRS),
            "Incorrect pair coverage")
    reference = {triple for triple in TRIPLES if triple[0] ^ triple[1] ^ triple[2] == 7}
    reported_reference = tuple(map(tuple, data["reference_triples"]))
    require(len(reference) == len(reported_reference) == 7
            and reference == set(reported_reference), "Incorrect CB reference triples")

    incident_pairs = {triple: tuple(combinations(triple, 2)) for triple in TRIPLES}
    pair_incidence = Counter(pair for triple in reference for pair in incident_pairs[triple])
    require(pair_incidence == Counter(PAIRS), "The Fano reference must saturate the pair caps")
    coefficients = {triple: scaled_cubic_coefficients(triple) for triple in TRIPLES}

    seen = set()
    denominators = set()
    strictly_slack = 0
    for record in data["certificates"]:
        monomial = tuple(record["monomial"])
        require(monomial in MONOMIALS and monomial not in seen,
                f"Invalid or repeated monomial {monomial}")
        seen.add(monomial)
        prices = dict(zip(pair_order, map(Fraction, record["prices"]), strict=True))
        require(all(price >= 0 for price in prices.values()),
                f"Negative packing multiplier for {monomial}")
        denominators.update(price.denominator for price in prices.values())

        for triple in TRIPLES:
            slack = sum(prices[pair] for pair in incident_pairs[triple]) - coefficients[triple][monomial]
            require(slack >= 0, f"Dual cap fails for {monomial}, triple {triple}")
            require(triple not in reference or slack == 0,
                    f"CB triple {triple} fails saturation for monomial {monomial}")
            strictly_slack += slack > 0
        require(sum(prices.values()) == sum(coefficients[triple][monomial] for triple in reference),
                f"Dual target fails for monomial {monomial}")
    require(seen == MONOMIALS, "Certificate omits spectral variables")
    return {
        "passed": True,
        "maximum_ratio_of_largest_to_smallest_probability": 3,
        "pairs_saturated_by_CB": len(pair_incidence),
        "triples": len(TRIPLES),
        "monomials": len(seen),
        "nonnegative_multipliers_checked": len(seen) * len(PAIRS),
        "dual_inequalities_checked": len(seen) * len(TRIPLES),
        "CB_saturations_checked": len(seen) * len(reference),
        "exact_dual_objective_matches": len(seen),
        "strictly_slack_inequalities": strictly_slack,
        "price_denominators": sorted(denominators),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    result = verify(json.loads(raw.decode("utf-8-sig")))
    result["certificate_sha256"] = sha256(raw).hexdigest()
    rendered = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
