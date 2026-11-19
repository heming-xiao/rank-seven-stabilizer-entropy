"""Exact affine-orbit equality check for all seven-point spectral tie patterns."""

from functools import reduce
from itertools import permutations
from operator import xor

from verify_rank7_forward_coefficients import REFERENCE, TRIPLES, UNIVERSE, coefficient_table


WEDGES = [sorted(UNIVERSE.difference(triple)) for triple in TRIPLES]
REFERENCE_DESIGN = tuple(i for i, triple in enumerate(TRIPLES) if triple in REFERENCE)


def design(placement):
    """Four-wedge indices whose placed labels form an affine plane."""
    return tuple(i for i, wedge in enumerate(WEDGES)
                 if reduce(xor, (placement[j] for j in wedge)) == 0)


def gap_mask(monomial):
    # The smallest positive probability, gap 6, is always present.
    return sum(1 << i for i in set(monomial) if i < 6)


def placed_colors(placement, colors):
    result = [0] * len(colors)
    for index, label in enumerate(placement):
        result[label] = colors[index]
    return tuple(result)


def verify():
    placements = [(placement, design(placement)) for placement in permutations(range(7))]
    group = [placement for placement, blocks in placements if blocks == REFERENCE_DESIGN]
    designs = {blocks for _, blocks in placements}
    if len(group) != 168 or len(designs) != 30:
        raise ArithmeticError("Unexpected seven-point affine geometry")
    for placement in group:
        # The extension fixes the absent point seven.
        offset = placement[0]
        images = [placement[i] ^ offset for i in (1, 2, 4)]
        extension = [
            reduce(xor, (images[i] for i in range(3) if label & (1 << i)), offset)
            for label in range(8)
        ]
        if tuple(extension[:7]) != placement or extension[7] != 7 or len(set(extension)) != 8:
            raise ArithmeticError("A design automorphism did not extend affinely")

    costs = coefficient_table()
    reference = {monomial: sum(cost[i] for i in REFERENCE_DESIGN)
                 for monomial, cost in costs.items()}
    deficits = {}
    for blocks in designs:
        masks = set()
        for monomial, cost in costs.items():
            loss = reference[monomial] - sum(cost[i] for i in blocks)
            if loss < 0:
                raise ArithmeticError("Reference plane value fails a forward coefficient")
            if loss:
                masks.add(gap_mask(monomial))
        deficits[blocks] = masks

    equalities = 0
    for active in range(1 << 6):
        colors = [sum(bool(active & (1 << j)) for j in range(i)) for i in range(7)]
        orbit = {placed_colors(placement, colors) for placement in group}
        for placement, blocks in placements:
            equal = not any(required & active == required for required in deficits[blocks])
            affine = placed_colors(placement, colors) in orbit
            if equal != affine:
                raise ArithmeticError(f"Equality mismatch for mask {active} and {placement}")
            equalities += equal
    print(f"{len(designs)} designs, {len(group)} affine automorphisms, "
          f"{len(designs) * len(costs)} exact forward coefficient comparisons.")
    print(f"{len(placements) * (1 << 6)} placement-and-tie cases; "
          f"{equalities} equalities, all affine colorings.")


if __name__ == "__main__":
    verify()
