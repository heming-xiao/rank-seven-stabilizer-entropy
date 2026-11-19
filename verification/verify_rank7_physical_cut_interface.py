"""Exact reference incidence and three-row rank-seven flag bounds."""

from fractions import Fraction
from itertools import combinations, permutations


HEADS = (0, 1, 2)
Q = (3, 4)
V = (5, 6)
TRIPLES = ((0, 1, 3), (0, 1, 4), (0, 2, 3), (0, 2, 4), (0, 1, 5), (0, 2, 6))
PLANES = {
    frozenset((a, b, c, d))
    for a, b, c, d in combinations(range(7), 4)
    if a ^ b ^ c ^ d == 0
}


def check_three_row_bound():
    bound = Fraction(19, 10**18)
    assert 4 * (2 * 10**14) * bound == Fraction(19, 1250)
    assert Fraction(1, 4) - bound / 2 > Fraction(249, 1000)
    assert Fraction(249, 1000)**3 > Fraction(19, 1250)


def check_reference():
    # An odd number of vertices in the affine basis (0,1,2,7)
    # represents each point uniquely, through binary XOR.
    assert len(PLANES) == 7
    assert all(sum({i, j} <= plane for plane in PLANES) == 2
               for i, j in combinations(range(7), 2))
    for head_order in permutations(HEADS):
        image = dict(zip((*HEADS, 7), (*head_order, 7)))
        for a, b, c in combinations((*HEADS, 7), 3):
            image[a ^ b ^ c] = image[a] ^ image[b] ^ image[c]
        assert set(image.values()) == set(range(8)) and image[3] == 3
        assert {frozenset(image[i] for i in plane) for plane in PLANES} == PLANES

        def weight(*labels):
            return int(frozenset(image[i] for i in labels) in PLANES)

        assert sum(weight(*HEADS, q) for q in Q) == 1
        assert sum(weight(*pair, *Q) for pair in combinations(HEADS, 2)) == 0
        assert sum(weight(0, *Q, v) for v in V) == 0
        assert all(sum(weight(*triple, i) for i in set(range(7)) - set(triple)) == 1
                   for triple in TRIPLES)
        assert sum(weight(0, *tail) for tail in combinations((*Q, *V), 3)) == 1

    # Enumerate all rankings of the three edges of the leading triangle.
    edges = tuple(combinations(HEADS, 2))
    for ranking in permutations((2, 1, 0)):
        anchor_rank = sorted(max(rank for edge, rank in zip(edges, ranking)
                                 if anchor in edge) for anchor in HEADS)
        assert anchor_rank == [1, 2, 2]



def check_fano_collar():
    assert 6 * 50176 * 12000 < 4 * 10**9
    assert 4 + Fraction(52, 3) * 12 == 212
    assert 2 * (1 - Fraction(424, 4 * 10**9))**2 > 1
    assert 16 * 212 < 4 * 10**9
    assert 448 * 560 == 250880
    assert 250880 * 231**3 > 4 * 10**9
    designs = {
        frozenset(frozenset(order[i] for i in plane) for plane in PLANES)
        for order in permutations(range(7))
    }
    assert len(designs) == 30
    for design in designs:
        assert len(design) == 7
        assert all(len(first & second) == 2 for first, second in combinations(design, 2))
        patterns = {tuple(sorted(tuple(sorted(plane)) for plane in design if i in plane))
                    for i in range(7)}
        assert len(patterns) == 7 and all(len(pattern) == 4 for pattern in patterns)


    triple_designs = set()
    expected_patterns = {(bool(mask & 1), bool(mask & 2), bool(mask & 4))
                         for mask in range(1, 8)}
    for design in designs:
        triples = set()
        for a, b, c in combinations(design, 3):
            if len(a & b & c) == 1:
                assert {(i in a, i in b, i in c) for i in range(7)} == expected_patterns
                triples.add(frozenset((a, b, c)))
        assert len(triples) == 28
        triple_designs.update(triples)
    assert len(triple_designs) == 840


if __name__ == "__main__":
    check_three_row_bound()
    check_reference()
    check_fano_collar()
    print("Three-row gap, reference incidences, and all 840 three-face Fano collar patterns verified exactly.")

