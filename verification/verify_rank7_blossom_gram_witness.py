"""Exact finite incidence and arithmetic checks for the blossom Gram exclusion."""

from fractions import Fraction as F
from itertools import combinations


LABELS = set(range(7))
TRIPLES = [frozenset(t) for t in combinations(sorted(LABELS), 3)]
WEDGES = [frozenset(LABELS - t) for t in TRIPLES]
TABLE = {
    frozenset(map(int, t)): F(k, 4)
    for k, row in [(3, "016"), (2, "034 145 246 356 456"), (1, "026 134 135 136 234 235 236")]
    for t in row.split()
}
WEIGHTS = {s: TABLE.get(frozenset(LABELS - s), F(0)) for s in WEDGES}


def label_set(text):
    return frozenset(map(int, text))


def surviving_partitions(anchor):
    pairs = set()
    for s in WEDGES:
        partner = frozenset((LABELS - s) | {anchor})
        if anchor in s and WEIGHTS[s] and WEIGHTS[partner]:
            pairs.add(frozenset((s, partner)))
    return pairs


def check_incidence():
    for anchor, products in [(0, ["0135 0246", "0145 0236"]),
                             (3, ["0236 1345"]), (4, ["0246 1345", "0146 2345"])]:
        assert sum(w for s, w in WEIGHTS.items() if anchor in s and 6 not in s) == 2
        expected = {frozenset(map(label_set, pair.split())) for pair in products}
        assert surviving_partitions(anchor) == expected
    for tri in "012 013 014 023 024 015 026".split():
        assert sum(w for s, w in WEIGHTS.items() if label_set(tri) <= s) == 1
    for left, right, expected in [("013", "014", [2, 5]), ("023", "024", [1, 6]), ("015", "026", [3, 4])]:
        x, y = label_set(left), label_set(right)
        both = [z for z in LABELS - (x | y) if WEIGHTS[x | {z}] and WEIGHTS[y | {z}]]
        assert sorted(both) == expected
    for s in ["0123", "0124", "0135", "0236"]:
        assert WEIGHTS[label_set(s)] == F(1, 2)
    for s in ["0145", "0246", "1345", "0146"]:
        assert WEIGHTS[label_set(s)] == F(1, 4)
    assert WEIGHTS[label_set("2345")] == F(3, 4)


def check_separating_matrix():
    columns = [t for t in TRIPLES if t in TABLE]
    rows = []
    for k in "06 16 26 34 35 36 45 46".split():
        rows.append((1, [int(label_set(k) <= t) for t in columns]))
    for k in "1345 1356 2346".split():
        rows.append((1, [int(t <= label_set(k)) for t in columns]))
    for present, absent in [(3, 0), (4, 0)]:
        rows.append((2, [int(present in t and absent not in t) for t in columns]))
    n = len(columns)
    assert n == len(rows) == 13
    for cap, row in rows:
        assert sum(x * TABLE[t] for x, t in zip(row, columns)) == cap
    augmented = [[F(k) for k in row] + [F(i == j) for j in range(n)] for i, (_, row) in enumerate(rows)]
    det = F(1)
    for i in range(n):
        p = next(j for j in range(i, n) if augmented[j][i])
        if p != i:
            augmented[p], augmented[i] = augmented[i], augmented[p]
            det *= -1
        pivot = augmented[i][i]
        det *= pivot
        augmented[i] = [z / pivot for z in augmented[i]]
        for j in range(n):
            if j != i:
                coefficient = augmented[j][i]
                augmented[j] = [a - coefficient * b for a, b in zip(augmented[j], augmented[i])]
    inverse_norm = max(sum(abs(x) for x in row[n:]) for row in augmented)
    assert abs(det) == 4 and inverse_norm == F(25, 4)


def check_robust_constants():
    eps, delta = F(1, 10**12), F(1, 10**6)
    a, b = F(7, 10), F(49, 100)
    assert a*a < F(1, 2) - eps and b*b < F(1, 4) - eps
    assert 26 * delta / (a*b) < 76 * delta
    assert (13 * delta + 5 * eps) / (a*b) < 40 * delta
    assert (4*eps + (F(1, 4) + eps)*192*delta) / (F(1, 4) - 2*eps) < 200*delta
    assert 14 / (a*b) < 42
    assert 360003 < 601**2
    # sqrt(1-y) >= 1-y is sufficient at the last contraction.
    assert b*b*(1-360000*eps) - 601*delta > F(23, 100) > (1202+13)*delta


if __name__ == "__main__":
    check_incidence()
    check_separating_matrix()
    check_robust_constants()
    print("Three blossom partitions, seven saturated triples, 13 independent rows and robust constants verified.")
