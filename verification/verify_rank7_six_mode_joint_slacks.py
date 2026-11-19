"""Verify the rank-six joint prices without numerical optimization."""

from itertools import combinations


LABELS = set(range(7))
TRIPLES = list(combinations(sorted(LABELS), 3))
WEDGES = [LABELS - set(triple) for triple in TRIPLES]
HEAD_EDGES = [(0, 1), (0, 2), (1, 2)]


def matchings(labels):
    if not labels:
        yield ()
        return
    first, *others = labels
    yield from matchings(others)
    for j, second in enumerate(others):
        for rest in matchings(others[:j] + others[j + 1 :]):
            yield ((first, second), *rest)


def check_matching_prices():
    count = 0
    reference = {
        (0, 1): [(0, 1), (2, 3), (4, 5)],
        (0, 2): [(0, 2), (1, 3), (4, 5)],
        (1, 2): [(1, 2), (0, 3), (4, 5)],
        None: [(0, 3), (1, 4), (2, 5)],
    }
    for matching in matchings(sorted(LABELS)):
        count += 1
        head = next((edge for edge in matching if edge in HEAD_EDGES), None)
        six_edges = sum(j < 6 for _, j in matching)
        five_ends = sum(int(i < 5) + int(j < 5) for i, j in matching)
        for a in range(7):
            for b in range(a, 7):
                def price(i, j):
                    return int(a >= i and b >= j) + int(a != b and b >= i and a >= j)

                optimum = sum(price(i, j) for i, j in reference[head])
                actual = sum(price(i, j) for i, j in matching)
                h_price = price(4, 5) - price(4, 6)
                r_price = price(4, 6) - price(5, 6)
                assert optimum - actual >= (3 - six_edges) * h_price + (5 - five_ends) * r_price
    assert count == 232
    return count


def check_slacks():
    weights = dict.fromkeys(TRIPLES, 0)
    for value, texts in [(3, ["016"]), (2, "034 145 246 356 456".split()),
                         (1, "026 134 135 136 234 235 236".split())]:
        for text in texts:
            weights[tuple(map(int, text))] = value
    for i, j in combinations(sorted(LABELS), 2):
        assert sum(w for t, w in weights.items() if i in t and j in t) <= 4
        assert 3 * sum(w for t, w in weights.items() if i not in t and j not in t) <= 28
    for four in combinations(sorted(LABELS), 4):
        assert sum(w for t, w in weights.items() if set(t) <= set(four)) <= 4
    for i in LABELS:
        for j in LABELS - {i}:
            assert sum(w for t, w in weights.items() if i in t and j not in t) <= 8

    sums = [0] * 8
    rows = [{1, 3, 4, 5}, {2, 3, 4, 6}, {2, 3, 5, 6}, {2, 4, 5, 6}, {3, 4, 5, 6}]
    for t, wedge in zip(TRIPLES, WEDGES):
        shared = sum(set(edge) <= wedge for edge in HEAD_EDGES[:2])
        highest = int({0, 1} <= wedge)
        high6 = highest * int(6 not in wedge)
        cover = sum({j, 6} <= set(t) for j in (3, 4, 5)) + sum(set(t) <= row for row in rows)
        assert cover - shared - 2 * high6 == int(t in [(0, 3, 6), (0, 4, 6), (0, 5, 6)])
        assert sum({0, 1, j} <= wedge for j in (2, 3, 4, 5)) == highest + high6
        triangle = sum(set(edge) <= wedge for edge in HEAD_EDGES)
        tri57 = sum(len((wedge - set(edge)) & set(range(5))) for edge in HEAD_EDGES if set(edge) <= wedge)
        features = [shared, highest, high6, shared * (6 not in wedge), triangle * (6 not in wedge),
                    tri57, triangle, int(6 not in wedge)]
        sums = [a + weights[t] * b for a, b in zip(sums, features)]
    assert sums == [18, 9, 7, 12, 16, 32, 24, 12]
    assert sum(w for t, w in weights.items() if {0, 1, 2}.isdisjoint(t)) == 4


if __name__ == "__main__":
    count = check_matching_prices()
    check_slacks()
    print(f"{count} matchings, {count * 28} exact coefficients, 119 packing rows and 35 price columns verified.")
