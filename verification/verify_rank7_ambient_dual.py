"""Independently check the ambient rank-7 packing certificates."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path

from verify_rank7_fano_dual import MONOMIALS, PAIRS, TRIPLES, VERTICES, cubic_coefficients, require


KNOWN = "unconditional_published_constraints"
CONDITIONAL = "conditional_on_physical_five_set_cap_two"


def expected_rows(include_five_set):
    rows = {("pair", support, 1) for support in PAIRS}
    rows.update(("four_set", support, 1) for support in combinations(VERTICES, 4))
    rows.update(("directed_link", support, 2) for support in permutations(VERTICES, 2))
    if include_five_set:
        rows.update(("five_set", support, 2) for support in combinations(VERTICES, 5))
    return rows


def support_for_row(kind, labels):
    """Identify the covered variables through their physical fourfold wedges."""
    vertices = set(VERTICES)
    label_set = set(labels)
    support = []
    for triple in TRIPLES:
        wedge = vertices.difference(triple)
        if kind == "pair":
            # The wedge lies in the other five labels.
            covered = wedge.isdisjoint(label_set)
        elif kind == "directed_link":
            # In six labels with the first label discarded, occupy the second.
            ignored, fixed = labels
            covered = ignored not in wedge and fixed in wedge
        else:
            # The wedge contains the triple/pair complementary to the row label.
            covered = vertices.difference(label_set) <= wedge
        if covered:
            support.append(triple)
    expected_size = {"pair": 5, "four_set": 4, "directed_link": 10, "five_set": 10}
    require(len(support) == expected_size[kind], f"Incorrect support size for {kind} {labels}")
    return support


def verify_packing(data, include_five_set, coefficients, reference):
    rows = tuple((row["kind"], tuple(row["labels"]), row["cap"]) for row in data["rows"])
    expected = expected_rows(include_five_set)
    require(len(rows) == len(expected) and set(rows) == expected,
            "Incorrect coverage, direction, or capacity in the packing rows")
    incident_rows = {triple: [] for triple in TRIPLES}
    cb_row_slack = []
    for index, (kind, labels, cap) in enumerate(rows):
        support = support_for_row(kind, labels)
        for triple in support:
            incident_rows[triple].append(index)
        slack = cap - len(reference.intersection(support))
        require(slack >= 0, f"CB infeasible for packing row {(kind, labels)}")
        cb_row_slack.append(slack)

    seen = set()
    multipliers = 0
    max_denominator = 1
    for certificate in data["certificates"]:
        monomial = tuple(certificate["difference_monomial_indices"])
        require(monomial in MONOMIALS and monomial not in seen,
                f"Invalid or repeated monomial record {monomial}")
        seen.add(monomial)
        prices = [Fraction(0)] * len(rows)
        for index, raw_price in certificate["nonzero_row_prices"]:
            require(type(index) is int and 0 <= index < len(rows) and not prices[index],
                    f"Invalid or repeated price index for {monomial}: {index}")
            price = Fraction(raw_price)
            require(price > 0, f"Nonpositive price for {monomial}, row {index}")
            require(cb_row_slack[index] == 0, f"Positive price on slack row {index}")
            prices[index] = price
            max_denominator = max(max_denominator, price.denominator)
            multipliers += 1

        for triple in TRIPLES:
            covered_price = sum(prices[index] for index in incident_rows[triple])
            coefficient = coefficients[triple][monomial]
            require(covered_price >= coefficient,
                    f"Infeasible dual bound for {monomial}, triple {triple}")
            require(triple not in reference or covered_price == coefficient,
                    f"Reference column is not tight for {monomial}, triple {triple}")

        objective = sum(price * cap for price, (_, _, cap) in zip(prices, rows))
        reference_value = sum(coefficients[triple][monomial] for triple in reference)
        require(objective == reference_value, f"Objective mismatch for {monomial}")

    missing = tuple(map(tuple, data["uncertified_monomial_indices"]))
    require(len(set(missing)) == len(missing) and set(missing) == MONOMIALS - seen,
            "Incomplete or incorrect accounting of uncertified monomials")
    return {
        "CB_feasible": True,
        "rows_by_kind": dict(Counter(kind for kind, _, _ in rows)),
        "packing_rows": len(rows),
        "certified_monomials": len(seen),
        "uncertified_monomials": sorted(missing),
        "dual_constraints_checked": len(seen) * len(TRIPLES),
        "CB_saturations_checked": len(seen) * len(reference),
        "exact_dual_objective_matches": len(seen),
        "positive_multipliers_checked": multipliers,
        "maximum_multiplier_denominator": max_denominator,
    }


def verify(data):
    require(tuple(data["vertex_labels"]) == VERTICES, "Unexpected vertex labels")
    coefficients = {triple: cubic_coefficients(triple) for triple in TRIPLES}
    reference = {triple for triple in TRIPLES if triple[0] ^ triple[1] ^ triple[2] == 7}
    require(len(reference) == 7, "Unexpected reference support")
    known = verify_packing(data[KNOWN], False, coefficients, reference)
    conditional = verify_packing(data[CONDITIONAL], True, coefficients, reference)
    missing = known["uncertified_monomials"]
    require(len(missing) == 9 and conditional["certified_monomials"] == len(MONOMIALS),
            "Unexpected certificate coverage")
    require(all({1, 2}.intersection(m) and {2, 3}.intersection(m) for m in missing),
            "A missing coefficient survives at least one of the proposed degeneracies")
    require((2, 2, 2) in missing and (1, 3, 3) in missing,
            "The reported exact vanishing condition needs rechecking")
    return {"passed": True, KNOWN: known, CONDITIONAL: conditional,
            "all_uncertified_terms_vanish_iff": "b2=0 and (b1=0 or b3=0)"}


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
