"""Verify the 84 rank-7 Fano LP duals using only the Python stdlib."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, combinations_with_replacement
import json
from pathlib import Path


VERTICES = tuple(range(7))
PAIRS = tuple(combinations(VERTICES, 2))
TRIPLES = tuple(combinations(VERTICES, 3))
MONOMIALS = set(combinations_with_replacement(VERTICES, 3))


def multiply_by_prefix(polynomial, last_variable):
    """Multiply a sparse polynomial by b_0 + ... + b_last_variable."""
    result = Counter()
    for monomial, coefficient in polynomial.items():
        for variable in range(last_variable + 1):
            key = tuple(sorted((*monomial, variable)))
            result[key] += coefficient
    return result


def cubic_coefficients(triple):
    polynomial = {(): 1}
    for vertex in triple:
        polynomial = multiply_by_prefix(polynomial, vertex)
    # Setting all b_i to 1 must give (i + 1)(j + 1)(k + 1).
    i, j, k = triple
    if sum(polynomial.values()) != (i + 1) * (j + 1) * (k + 1):
        raise AssertionError(f"Incorrect coefficient sum for triple {triple}")
    return polynomial


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify(data):
    require(tuple(data["vertex_labels"]) == VERTICES, "Unexpected vertex labels")
    pair_order = tuple(map(tuple, data["pair_order"]))
    require(len(pair_order) == len(PAIRS) and set(pair_order) == set(PAIRS),
            "Incorrect pair coverage")

    reference = {triple for triple in TRIPLES if triple[0] ^ triple[1] ^ triple[2] == 7}
    reported_reference = tuple(map(tuple, data["reference_triples"]))
    require(len(reference) == len(reported_reference) == 7
            and reference == set(reported_reference), "Incorrect CB reference triples")
    triple_pairs = {triple: tuple(combinations(triple, 2)) for triple in TRIPLES}
    reference_incidence = Counter(pair for triple in reference for pair in triple_pairs[triple])
    require(reference_incidence == Counter(PAIRS), "CB is not primal feasible")

    coefficients = {triple: cubic_coefficients(triple) for triple in TRIPLES}
    # The triple (4, 5, 6) has the largest prefix in every sorted position.
    supported = {monomial for monomial in MONOMIALS
                 if all(index <= vertex for index, vertex in zip(monomial, (4, 5, 6)))}
    require(set.union(*(set(cubic) for cubic in coefficients.values())) == supported,
            "Direct cubic expansion has incorrect monomial support")
    seen = set()
    price_denominators = set()
    strictly_slack = 0
    min_positive_slack = None
    for entry in data["coefficient_certificates"]:
        monomial = tuple(entry["difference_monomial_indices"])
        require(monomial in MONOMIALS and monomial not in seen,
                f"Invalid or repeated monomial {monomial}")
        seen.add(monomial)
        prices = dict(zip(pair_order, map(Fraction, entry["pair_prices"]), strict=True))
        price_denominators.update(value.denominator for value in prices.values())
        for triple in TRIPLES:
            slack = sum(prices[pair] for pair in triple_pairs[triple]) - coefficients[triple][monomial]
            require(slack >= 0, f"Dual infeasible for monomial {monomial}, triple {triple}")
            if slack > 0:
                require(triple not in reference,
                        f"CB triple {triple} fails saturation for monomial {monomial}")
                strictly_slack += 1
                if min_positive_slack is None or slack < min_positive_slack:
                    min_positive_slack = slack
        dual_objective = sum(prices.values())
        cb_objective = sum(coefficients[triple][monomial] for triple in reference)
        require(dual_objective == cb_objective, f"Dual objective mismatch for monomial {monomial}")
    require(seen == MONOMIALS, "Certificate omits difference monomials")

    return {
        "passed": True,
        "vertices": len(VERTICES),
        "pairs_covered_exactly_once_by_CB": len(reference_incidence),
        "triples": len(TRIPLES),
        "difference_monomials": len(seen),
        "monomials_with_nonzero_coefficient_in_some_triple": len(supported),
        "dual_constraints_checked": len(seen) * len(TRIPLES),
        "CB_saturations_checked": len(seen) * len(reference),
        "exact_dual_objective_matches": len(seen),
        "price_denominators": sorted(price_denominators),
        "strictly_slack_constraints": strictly_slack,
        "minimum_positive_slack": str(min_positive_slack),
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
