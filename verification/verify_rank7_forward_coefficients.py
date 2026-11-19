"""Exact quartic packing audit in forward Schmidt probability differences.

Verification needs only the standard library. To regenerate the sparse
certificate, pass --generate in an environment with SciPy installed.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, combinations_with_replacement
import json
from math import prod
from pathlib import Path

from verify_rank7_ambient_dual import expected_rows, support_for_row
from verify_rank7_fano_dual import TRIPLES, VERTICES, require


UNIVERSE = frozenset(VERTICES)
MONOMIALS = tuple(combinations_with_replacement(VERTICES, 4))
REFERENCE = frozenset(triple for triple in TRIPLES if triple[0] ^ triple[1] ^ triple[2] == 7)
KNOWN_ROWS = tuple(sorted(expected_rows(False)))
CAP_01 = ("five_set", (2, 3, 4, 5, 6), 2)
CAP_02 = ("five_set", (1, 3, 4, 5, 6), 2)
EXTRA_ROWS = (CAP_01, CAP_02)
ALL_ROWS = KNOWN_ROWS + EXTRA_ROWS
EXCEPTION_DUALS = {
    (0, 1, 6, 6): (CAP_01,),
    (0, 2, 5, 6): (CAP_01, CAP_02, ("directed_link", (6, 0), 2), ("four_set", (3, 4, 5, 6), 1)),
    (0, 2, 6, 6): (CAP_01, CAP_02),
    (1, 1, 6, 6): (CAP_01,),
    (1, 2, 6, 6): (CAP_01, *(('pair', pair, 1) for pair in combinations((3, 4, 5, 6), 2))),
}


def coefficient_table():
    """Expand each physical four-wedge probability product by suffix multiplication."""
    polynomials = []
    for triple in TRIPLES:
        wedge = sorted(UNIVERSE.difference(triple))
        polynomial = {(): 1}
        for label in wedge:
            updated = Counter()
            for monomial, coefficient in polynomial.items():
                for variable in range(label, 7):
                    updated[tuple(sorted((*monomial, variable)))] += coefficient
            polynomial = updated
        require(sum(polynomial.values()) == prod(7 - label for label in wedge),
                f"Incorrect expansion mass for {tuple(wedge)}")
        polynomials.append(polynomial)
    return {monomial: [polynomial[monomial] for polynomial in polynomials] for monomial in MONOMIALS}


def row_table():
    supports = [set(support_for_row(kind, labels)) for kind, labels, _ in ALL_ROWS]
    return [[int(triple in support) for triple in TRIPLES] for support in supports]


def make_certificate():
    from scipy.optimize import linprog

    costs = coefficient_table()
    matrix = row_table()[:len(KNOWN_ROWS)]
    capacities = [cap for _, _, cap in KNOWN_ROWS]
    certificates, exceptions = [], []
    for monomial, cost in costs.items():
        result = linprog([-c for c in cost], A_ub=matrix, b_ub=capacities,
                         bounds=(0, None), method="highs")
        require(result.success, f"LP failed for {monomial}: {result.message}")
        prices = [Fraction(float(-value)).limit_denominator(1_000_000)
                  for value in result.ineqlin.marginals]
        sparse_prices = [[i, str(price)] for i, price in enumerate(prices) if price]
        if monomial in EXCEPTION_DUALS:
            weights = [Fraction(float(value)).limit_denominator(1_000_000) for value in result.x]
            exceptions.append({
                "monomial": monomial,
                "old_dual_prices": sparse_prices,
                "old_primal_weights": [[i, str(value)] for i, value in enumerate(weights) if value],
                "conditional_dual_prices": [[ALL_ROWS.index(row), "1"] for row in EXCEPTION_DUALS[monomial]],
            })
        else:
            certificates.append({"monomial": monomial, "prices": sparse_prices})
    return {
        "vertex_labels": VERTICES,
        "reference_triples": sorted(REFERENCE),
        "rows": [{"kind": kind, "labels": labels, "cap": cap} for kind, labels, cap in ALL_ROWS],
        "old_certificates": certificates,
        "exceptions": exceptions,
    }


def sparse_vector(raw, size):
    values = [Fraction(0)] * size
    for index, value in raw:
        require(type(index) is int and 0 <= index < size and not values[index],
                f"Invalid or repeated index {index}")
        values[index] = Fraction(value)
        require(values[index] > 0, f"Nonpositive stored coefficient at {index}")
    return values


def verify_dual(raw, matrix, capacities, costs):
    prices = sparse_vector(raw, len(capacities))
    for j, cost in enumerate(costs):
        lhs = sum(price * row[j] for price, row in zip(prices, matrix))
        require(lhs >= cost, f"Dual upper bound fails for triple {TRIPLES[j]}")
    return sum(price * cap for price, cap in zip(prices, capacities))


def verify(data):
    require(tuple(data["vertex_labels"]) == VERTICES, "Unexpected vertex labels")
    reported = tuple(map(tuple, data["reference_triples"]))
    require(len(REFERENCE) == len(reported) == 7 and set(reported) == REFERENCE,
            "Incorrect Fano reference")
    rows = [(row["kind"], tuple(row["labels"]), row["cap"]) for row in data["rows"]]
    require(tuple(rows) == ALL_ROWS, "Unexpected old or conditional rows")
    matrix, costs = row_table(), coefficient_table()
    capacities = [row[2] for row in rows]
    reference = [int(triple in REFERENCE) for triple in TRIPLES]
    for coefficients, cap in zip(matrix, capacities):
        require(sum(c * x for c, x in zip(coefficients, reference)) <= cap, "Fano is infeasible")
    old_size = len(KNOWN_ROWS)
    old_matrix, old_caps = matrix[:old_size], capacities[:old_size]
    seen = set()
    for record in data["old_certificates"]:
        monomial = tuple(record["monomial"])
        require(monomial in costs and monomial not in seen and monomial not in EXCEPTION_DUALS,
                f"Invalid old record {monomial}")
        seen.add(monomial)
        cost = costs[monomial]
        cb_value = sum(c*x for c, x in zip(cost, reference))
        require(verify_dual(record["prices"], old_matrix, old_caps, cost) == cb_value,
                f"Old dual does not match Fano for {monomial}")
    require(seen == set(MONOMIALS).difference(EXCEPTION_DUALS), "Incomplete old coverage")

    exceptions = {}
    for record in data["exceptions"]:
        monomial = tuple(record["monomial"])
        require(monomial in EXCEPTION_DUALS and monomial not in exceptions, f"Invalid exception {monomial}")
        cost = costs[monomial]
        cb_value = sum(c*x for c, x in zip(cost, reference))
        witness = sparse_vector(record["old_primal_weights"], len(TRIPLES))
        for row, cap in zip(old_matrix, old_caps):
            require(sum(c*x for c, x in zip(row, witness)) <= cap, f"Witness infeasible for {monomial}")
        witness_value = sum(c*x for c, x in zip(cost, witness))
        require(witness_value > cb_value, f"Witness does not exceed Fano for {monomial}")
        require(verify_dual(record["old_dual_prices"], old_matrix, old_caps, cost) == witness_value,
                f"Old witness does not match a dual upper bound for {monomial}")
        explicit = {ALL_ROWS.index(row): Fraction(1) for row in EXCEPTION_DUALS[monomial]}
        require(sparse_vector(record["conditional_dual_prices"], len(rows)) ==
                [explicit.get(i, 0) for i in range(len(rows))], f"Unexpected conditional reduction for {monomial}")
        require(verify_dual(record["conditional_dual_prices"], matrix, capacities, cost) == cb_value,
                f"Conditional dual does not match Fano for {monomial}")
        exceptions["".join(map(str, monomial))] = {
            "CB_value": cb_value,
            "exact_old_packing_optimum": str(witness_value),
            "conditional_optimum": cb_value,
        }
    require(len(exceptions) == len(EXCEPTION_DUALS), "Incomplete exception coverage")
    return {
        "passed": True,
        "monomials": len(MONOMIALS),
        "monomials_occurring_in_some_triple": sum(any(cost) for cost in costs.values()),
        "old_packing_rows": len(KNOWN_ROWS),
        "old_certified_monomials": len(seen),
        "conditional_certified_monomials": len(seen) + len(exceptions),
        "conditional_fixed_pairs": [[0, 1], [0, 2]],
        "dual_inequalities_checked": (len(seen) + 2 * len(exceptions)) * len(TRIPLES),
        "exception_optima": exceptions,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--generate", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.generate:
        data = make_certificate()
        verify(data)
        args.certificate.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    raw = args.certificate.read_bytes()
    result = verify(json.loads(raw.decode("utf-8-sig")))
    result["certificate_sha256"] = sha256(raw).hexdigest()
    rendered = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
