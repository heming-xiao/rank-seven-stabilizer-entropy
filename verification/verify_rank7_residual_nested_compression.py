"""Exact three-cell certificate for the residual spectrum, using only exterior compression.

Run without arguments to verify the stored rational certificate using the standard library.
Pass --generate to rediscover sparse prices with SciPy and SymPy, then verify them.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from math import ceil, floor, isqrt, prod
from pathlib import Path

from verify_rank7_forward_coefficients import KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE, row_table


PROBABILITIES = tuple(F(x, 10) for x in (79, 38, 17, 14, 13, 11, 10))
WEDGES = [UNIVERSE.difference(triple) for triple in TRIPLES]
SCORES = [prod(PROBABILITIES[i] for i in wedge) for wedge in WEDGES]
REFERENCE_COST = sum(cost for cost, triple in zip(SCORES, TRIPLES) if triple in REFERENCE)
ORDER = sorted(range(35), key=SCORES.__getitem__)
RAYS = [[int(i in ORDER[j:]) for i in range(35)] for j in range(35)]
RATE = F(44, 25)
CERT = (Path(__file__).resolve().parents[1] / "certificates" / "rank7" / "rank7_residual_nested_compression.json")


def lower_gap_squared(j):
    # Rationally enclose square roots on a fine grid, then round the squared gap down.
    scale = 10**6
    hi = SCORES[ORDER[j]]
    lo = SCORES[ORDER[j-1]] if j else F(0)
    high_root_lower = isqrt(floor(hi*scale**2))
    low_root_upper = isqrt(floor(lo*scale**2))
    if low_root_upper**2 != lo*scale**2:
        low_root_upper += 1
    gap = max(F(high_root_lower-low_root_upper, scale), 0)
    return F(floor(gap**2*10000), 10000)


GAPS = [lower_gap_squared(j) for j in range(35)]
SELECTED = sorted(sorted(range(35), key=lambda j: -GAPS[j])[:16])


def cell_rows(cell):
    matrix = [list(r) for r in row_table()[:len(KNOWN_ROWS)]]
    caps = [F(row[2]) for row in KNOWN_ROWS]
    for pair in combinations(range(7), 2):
        matrix.append([int(set(pair) <= wedge) for wedge in WEDGES])
        caps.append(F(7, 3))
    matrix.append([-v for v in SCORES])
    caps.append(-REFERENCE_COST)
    if cell == 0:
        branches = [(0, 1, F(19,3))]
    elif cell == 1:
        branches = [(0, -1, F(19,3)), (17, -1, F(7,2))]
    elif cell == 2:
        branches = [(0, -1, F(19,3)), (17, 1, F(7,2))]
    else:
        raise ValueError("Unknown certificate cell")
    for j, sign, cut in branches:
        matrix.append([sign*val for val in RAYS[j]])
        caps.append(sign*cut)
    return matrix, caps


def unpack(pairs, size):
    out = [F(0)]*size
    for i, v in pairs:
        if not 0 <= i < size or out[i] or F(v) <= 0:
            raise ArithmeticError("Incorrect sparse dual price")
        out[i] = F(v)
    return out


def priced(matrix, caps, advertised, cost, box_correction=False):
    y = unpack(advertised, len(caps))
    active = [(row, cap, p) for row, cap, p in zip(matrix, caps, y) if p]
    bound = sum(cap*p for _, cap, p in active)
    for i, target in enumerate(cost):
        excess = target - sum(row[i]*p for row, _, p in active)
        if excess > 0:
            if not box_correction:
                raise ArithmeticError(f"Incorrect terminal dual at column {i}, deficit {excess}")
            # The only columns present in trace-range searches are the 35 physical
            # occupancies, each at most one by the physical complement-pair bounds.
            bound += excess
    return bound


def phi(x):
    rem = x - floor(x)
    return rem*(1-rem)


def lower_segments(lo, hi):
    if lo > hi:
        raise ArithmeticError("Inverted trace range")
    points = sorted(set([lo, hi, *range(ceil(lo), floor(hi)+1)]))
    if len(points) == 1:
        return [(F(0), phi(points[0]))]
    lines = []
    for u, v in zip(points, points[1:]):
        slope = (phi(v)-phi(u))/(v-u)
        lines.append((slope, phi(u)-slope*u))
    # Chords lie below phi on their own unit intervals by concavity. Increasing
    # slopes imply their affine extensions lie below the chord chain globally.
    if any(a[0] > b[0] for a,b in zip(lines,lines[1:])):
        raise ArithmeticError("Nonconvex chord chain")
    return lines


def terminal_rows(cell, record):
    physical, caps = cell_rows(cell)
    n = len(SELECTED)
    matrix = [r+[0]*n for r in physical]
    terminal_caps = caps.copy()
    for p,j in enumerate(SELECTED):
        entry = record["range_prices"][str(j)]
        lower = -priced(physical, caps, entry[0], [-x for x in RAYS[j]], True)
        upper = priced(physical, caps, entry[1], RAYS[j], True)
        lo = F(floor(lower*10000), 10000)
        hi = F(ceil(upper*10000), 10000)
        for slope, intercept in lower_segments(lo,hi):
            row = [slope*v for v in RAYS[j]]+[0]*n
            row[35+p] = -1
            matrix.append(row)
            terminal_caps.append(-intercept)
    cost = [RATE*v for v in SCORES]+[-GAPS[j] for j in SELECTED]
    return matrix,terminal_caps,cost


def generate():
    import numpy as np
    from scipy.optimize import linprog
    import sympy as sp
    def as_float(a):
        return np.array(a, dtype=float)
    def maximum(a,b,objective):
        result = linprog(-as_float(objective), A_ub=as_float(a), b_ub=as_float(b), bounds=(0,None))
        if not result.success:
            raise ArithmeticError(result.message)
        return result
    def approximate_prices(result):
        vals = [F(round(-v*10**8),10**8) for v in result.ineqlin.marginals]
        return [[i,str(v)] for i,v in enumerate(vals) if v>0]
    def exact_prices(a,b,c,result):
        initial = [-s for s in result.ineqlin.marginals]
        support = [i for i,v in enumerate(initial) if v>1e-8]
        reduced = as_float(a)[support].T @ np.array([initial[i] for i in support])-as_float(c)
        candidates = sorted(range(len(c)), key=lambda j:(result.x[j]<1e-8, abs(reduced[j])))
        cols = [j for j in candidates if abs(reduced[j])<1e-6]
        equations = sp.Matrix([[a[i][j] for i in support] for j in cols])
        _, indexes = equations.T.rref()
        if len(indexes) != len(support):
            raise ArithmeticError("Incomplete terminal basis")
        sol = equations[list(indexes),:].inv()*sp.Matrix([c[cols[k]] for k in indexes])
        out = [[i,str(v)] for i,v in zip(support,sol) if v]
        priced(a,b,out,c)
        return out
    records = []
    for cell in range(3):
        physical,caps = cell_rows(cell)
        record = {"range_prices":{}}
        for j in SELECTED:
            record["range_prices"][str(j)] = [
                approximate_prices(maximum(physical,caps,[sgn*x for x in RAYS[j]]))
                for sgn in (-1,1)]
        matrix,terminal_caps,cost = terminal_rows(cell,record)
        result = maximum(matrix,terminal_caps,cost)
        record["terminal_prices"] = exact_prices(matrix,terminal_caps,cost,result)
        records.append(record)
    return records


def verify(records):
    if len(records) != 3 or len(set(SCORES)) != 35:
        raise ArithmeticError("Wrong number of cells or distinct amplitudes")
    for cell, record in enumerate(records):
        matrix,caps,cost = terminal_rows(cell,record)
        upper = priced(matrix,caps,record["terminal_prices"],cost)
        margin = RATE*REFERENCE_COST-upper
        if margin < 0:
            raise ArithmeticError(f"Cell {cell} fails by {-margin}")
        print(f"Cell {cell+1}: terminal rational margin {float(margin):.9f} (exact sign verified).")
    print("Three cells, 96 trace endpoints, and all terminal columns verified exactly.")
    print("For every physical frame with E >= 0, exterior compression D >= (44/25)*E.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate",action="store_true")
    args = parser.parse_args()
    if args.generate:
        result = generate()
        verify(result)
        CERT.write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8")
    else:
        verify(json.loads(CERT.read_text(encoding="utf-8")))

