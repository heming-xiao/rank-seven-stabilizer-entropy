"""Verify the two rank-seven cone certificates with no bound on full spread."""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
import json
from math import prod
from pathlib import Path

from verify_rank7_ambient_dual import verify_packing
from verify_rank7_fano_dual import MONOMIALS, TRIPLES, VERTICES, require


PARAMETERS = {
    "largest_five_probability_ratio_at_most_three": ((1, 2, 3, 4), 1, 2),
    "middle_inverse_gap_at_most_largest_probability_inverse": ((2, 3), 1, 1),
}


def scaled_cubic(triple, shifted, numerator, scale):
    """Expand the product of independent weighted prefix forms by multiplication."""
    polynomial = {(): 1}
    for vertex in triple:
        linear = [scale] + [scale * int(i <= vertex) + numerator * int(i in shifted)
                            for i in range(1, 7)]
        expanded = Counter()
        for indices, coefficient in polynomial.items():
            for index, multiplier in enumerate(linear):
                if multiplier:
                    expanded[tuple(sorted((*indices, index)))] += coefficient * multiplier
        polynomial = expanded
    require(set(polynomial) <= MONOMIALS, f"Expansion degree failed for {triple}")
    expected_mass = prod(scale * (1 + vertex) + numerator * len(shifted) for vertex in triple)
    require(sum(polynomial.values()) == expected_mass, f"Expansion mass failed for {triple}")
    return polynomial


def verify(data):
    require(tuple(data["vertex_labels"]) == VERTICES, "Unexpected vertex labels")
    reference = {triple for triple in TRIPLES if triple[0] ^ triple[1] ^ triple[2] == 7}
    reported = tuple(map(tuple, data["reference_triples"]))
    require(len(reference) == len(reported) == 7 and set(reported) == reference,
            "Incorrect computational-basis reference")
    checked = {}
    for cone in data["cones"]:
        name = cone["name"]
        require(name in PARAMETERS and name not in checked, f"Invalid or repeated cone {name}")
        parameters = (tuple(cone["obligated_differences"]), cone["shift_numerator"], cone["scale"])
        require(parameters == PARAMETERS[name], f"Incorrect substitution for {name}")
        coefficients = {triple: scaled_cubic(triple, *parameters) for triple in TRIPLES}
        normalized = {
            "rows": data["rows"],
            "certificates": [
                {"difference_monomial_indices": record["monomial"],
                 "nonzero_row_prices": record["nonzero_row_prices"]}
                for record in cone["certificates"]
            ],
            "uncertified_monomial_indices": [],
        }
        evidence = verify_packing(normalized, False, coefficients, reference)
        evidence["scaled_objective_factor"] = parameters[2] ** 3
        evidence["monomials_occurring_in_some_triple"] = len(
            set.union(*(set(values) for values in coefficients.values())))
        checked[name] = evidence
    require(set(checked) == set(PARAMETERS), "Incomplete cone coverage")
    return {"passed": True, "cones": checked}


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
