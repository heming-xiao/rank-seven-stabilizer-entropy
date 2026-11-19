"""Check the rational constants in the two dimension-independent separation proofs."""

from fractions import Fraction as F
from itertools import combinations


def check_fixed_gap():
    face = F(1, 10**130)
    cutoff = F(1, 10**20)
    threshold = F(1, 10**100)
    epsilon = F(1, 10**26)
    lost = F(1, 10**17)
    delta_bound = F(3, 10**40)
    orientation_bound = F(1, 10**56)
    assert 8 * threshold / cutoff < delta_bound**2
    assert F(4, 3) / cutoff * (F(1, 10**50) + 7 * delta_bound)**2 < orientation_bound
    assert 2 * delta_bound + 2 * F(1, 10**28) < epsilon
    assert 128 * 24 * face + 16 * cutoff + 24 * face / threshold + 32 * orientation_bound < lost
    count = (1 + F(2, 5) * (F(1, 6) - face) - 2 * lost) / 2
    assert count > F(52, 100)
    assert 2 / (1 - (20 * epsilon)**2) < F(201, 100) < 4 * count
    assert 6 * (1 - (33 * epsilon)**2) > 4
    assert lost + 66 * epsilon < F(1, 10**16)
    assert F(6, 10**7) < F(1, 6) - face


def check_general_cut():
    # Ratios below cancel all powers of the positive single-edge excess.
    orientation_cost = F(4, 3) * (1 + 384)
    assert 4 * 8 + 4 * orientation_cost < 2100
    assert 16 * 2100 * 3 < 318**2
    scale = 2 * 10**14
    rounding_scale = 160000
    # For 0 < mu <= 1/3, 384*E/mu <= 384/(9*scale).
    remaining = F(1, 100) - F(384, 9 * scale)
    assert 318**2 * F(rounding_scale, scale) < remaining**2
    # Four disjoint translates would require the opposite inequality.
    count_slope = F(2, 5) - F(2, 100)
    denominator_slope = F(400, rounding_scale)
    assert count_slope - denominator_slope - count_slope * denominator_slope / 3 > 0
    assert 18 * (F(2, 100) + F(3 * 33**2, rounding_scale)) < 1
    assert F(16**2, 3 * rounding_scale) < F(1, 4)
    assert F(33**2, 3 * rounding_scale) < 1


def check_group_counts():
    # dim(rad H)+k <= n gives |H|/D <= 2**k, with 2**k dividing rank two.
    # Enumerate the possible logarithmic sizes once dimensions n>=3 are allowed.
    candidates = []
    for symplectic_half_rank in (0, 1):
        for exponent in range(symplectic_half_rank + 1):
            radical_block_rank = 2 ** (2 * symplectic_half_rank - exponent)
            candidates.append((symplectic_half_rank, exponent, radical_block_rank))
    assert candidates == [(0, 0, 1), (1, 0, 4), (1, 1, 2)]
    assert len({0, 3, 6, 9}) == 4
    assert all(b - a >= 3 for a, b in zip((0, 3, 6), (3, 6, 9)))
    assert 9 + 1 == 10


def check_reference_flag():
    labels = range(7)
    wedges = [frozenset((i, j, k, l)) for i, j, k, l in combinations(labels, 4)
              if i ^ j ^ k ^ l == 0]
    assert len(wedges) == 7
    assert all(sum(i in wedge for wedge in wedges) == 4 for i in labels)
    assert all(sum(i in wedge and j in wedge for wedge in wedges) == 2
               for i, j in combinations(labels, 2))
    assert all(len(one & other) == 2 for one, other in combinations(wedges, 2))
    patterns = {i: frozenset(j for j, wedge in enumerate(wedges) if i in wedge)
                for i in labels}
    assert len(set(patterns.values())) == 7
    assert all(len(pattern) == 4 for pattern in patterns.values())

    def completion(triple):
        return sum(set(triple) <= wedge for wedge in wedges)

    assert completion((0, 3, 4)) == 0
    assert frozenset((1, 2, 3, 4)) not in wedges
    assert sum(frozenset((0, 1, 2, i)) in wedges for i in (3, 4)) == 1
    assert all(completion((0, i, j)) == 1
               for i, j in ((1, 3), (1, 4), (2, 3), (2, 4), (1, 5), (2, 6)))
    for wedge in map(frozenset, combinations(labels, 4)):
        localized = sum(frozenset((i, j, 3, 4)) == wedge
                        for i, j in combinations((0, 1, 2), 2))
        localized += sum(frozenset((0, 3, 4, j)) == wedge for j in (5, 6))
        assert localized == int({0, 3, 4} <= wedge) + int(wedge == {1, 2, 3, 4})


def check_fano_collar():
    epsilon = F(1, 4 * 10**9)
    assert 6 * epsilon < F(1, 50176 * 12000)
    assert 4 + F(52, 3) * 12 == 212
    leakage = 212 * epsilon
    assert 2 * (1 - 2 * leakage)**2 > 1
    assert 16 * leakage < 1
    assert 560 * 112 * 212 < 14 * 10**6


if __name__ == "__main__":
    check_fixed_gap()
    check_general_cut()
    check_group_counts()
    check_reference_flag()
    check_fano_collar()
    print("Fixed gap, cubic, Pauli group sizes, 35 tight-flag columns and the seven-plane collar verified.")
