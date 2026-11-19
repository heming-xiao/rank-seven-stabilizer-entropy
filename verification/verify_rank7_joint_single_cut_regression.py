"""Verify a combined mixed, anticommuting and one-cut compression proof.

All inequalities are exact; the optional --generate mode rediscovers the two LP prices.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from math import ceil, floor, isqrt, prod
from pathlib import Path
from verify_rank7_forward_coefficients import KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE, row_table


SPECTRUM = tuple(map(F, ("19.32", "4.69", "4.13", "1.012", "1.008", "1.004", "1")))
WEDGES = [UNIVERSE.difference(t) for t in TRIPLES]
COSTS = [prod(SPECTRUM[i] for i in w) for w in WEDGES]
REF = [int(t in REFERENCE) for t in TRIPLES]
CUT = [int(0 in w and bool({1,2} & w)) for w in WEDGES]
MATRIX = row_table()[:len(KNOWN_ROWS)]
CAPS = [r[2] for r in KNOWN_ROWS]
CERT = (Path(__file__).resolve().parents[1] / "certificates" / "rank7" / "rank7_joint_single_cut_regression.json")


def dot(x,y):
    return sum(a*b for a,b in zip(x,y,strict=True))


def objectives():
    alpha,beta,gamma,a,b,c,d = SPECTRUM
    h,k,q = alpha-beta, beta-gamma, gamma-a
    g = h*q
    delta = k*(alpha-a)
    G = g - F(200,11)*b*(c-d)
    R = k**2*(k**2+(h**2+q**2)/2)
    pay = []
    for w in WEDGES:
        u1 = prod(SPECTRUM[i] for i in w-{0,1}) if {0,1} <= w else 0
        u2 = prod(SPECTRUM[i] for i in w-{0,2}) if {0,2} <= w else 0
        v = int({0,1} <= w)
        shared = v + int({0,2} <= w)
        pay.append(24*G*(u1+u2) + 24*delta*u1
                   + (12*G**2+g**2)*shared/12 + (12*delta**2+R)*v/F(5,2))
    if G <= 0 or dot(CUT,REF) != 3:
        raise ArithmeticError("Wrong geometry or invalid shift")
    lower_edge = min(score for score,inside in zip(COSTS,CUT) if inside)
    upper_edge = max(score for score,inside in zip(COSTS,CUT) if not inside)
    if not (lower_edge > upper_edge and lower_edge + upper_edge > 20
            and (lower_edge+upper_edge-20)**2 > 4*lower_edge*upper_edge):
        raise ArithmeticError("Squared amplitude gap is not greater than 20")
    charge = [F(21,20)*168*e-p-768*r for e,p,r in zip(COSTS,pay,CUT)]
    cap = [e+200*r for e,r in zip(COSTS,CUT)]
    return [(cap, dot(COSTS,REF)+200*F(18,5)), (charge,dot(charge,REF))]


def verify_obstruction():
    # Ordering is TRIPLES (the complementary labels). These occupancies obstruct
    # the full standard nested-threshold estimate if used without other defects.
    sixths = [1,0,0,2,3,0,0,2,2,3,0,0,0,0,0,0,0,0,0,1,1,2,3,0,0,2,2,1,0,3,0,0,0,3,3]
    x = [F(v,6) for v in sixths]
    for row,cap in zip(MATRIX,CAPS):
        if dot(row,x)>cap:
            raise ArithmeticError("Obstruction violates packing")
    for pair in combinations(range(7),2):
        if sum(v for w,v in zip(WEDGES,x) if set(pair)<=w)>F(7,3):
            raise ArithmeticError("Obstruction violates a pair cap")
    order = sorted(range(35), key=COSTS.__getitem__)
    upper = F(0)
    previous_lo = F(0)
    scale = 10**6
    for pos,i in enumerate(order):
        root_lo_int = isqrt(floor(COSTS[i]*scale**2))
        lo = F(root_lo_int,scale)
        hi = lo if lo*lo==COSTS[i] else lo+F(1,scale)
        fraction = sum(x[j] for j in order[pos:]) % 1
        upper += (hi-previous_lo)**2*fraction*(1-fraction)
        previous_lo = lo
    e = dot(COSTS,x)-dot(COSTS,REF)
    if F(7,4)*e-upper <= 14:
        raise ArithmeticError("The upper bound fails to certify the nested-only obstruction")
    print("A feasible sixths array misses the compression-only nested target by more than 14.")


def generate(targets):
    from scipy.optimize import linprog
    import numpy as np
    import sympy as sp
    results = []
    mat = np.array(MATRIX)
    for cost,_ in targets:
        lp = linprog(-np.array(cost,dtype=float),A_ub=mat,b_ub=CAPS,bounds=(0,None))
        if not lp.success:
            raise ArithmeticError(lp.message)
        supp = [i for i,v in enumerate(lp.ineqlin.marginals) if -v>1e-8]
        reduced = -mat[supp].T @ lp.ineqlin.marginals[supp]-np.array(cost,dtype=float)
        cols = sorted([j for j,v in enumerate(reduced) if abs(v)<1e-6], key=lambda j:lp.x[j]<1e-8)
        eq = sp.Matrix([[MATRIX[i][j] for i in supp] for j in cols])
        _, pivots = eq.T.rref()
        if len(pivots) != len(supp):
            raise ArithmeticError("Incomplete rational price basis")
        y = eq[list(pivots),:].inv()*sp.Matrix([cost[cols[j]] for j in pivots])
        results.append([[i,str(v)] for i,v in zip(supp,y) if v])
    return results


def verify(records,targets):
    for n,((cost,target),entries) in enumerate(zip(targets,records,strict=True)):
        prices = [F(0)]*len(CAPS)
        for i,v in entries:
            if not 0<=i<len(CAPS) or prices[i] or F(v)<=0:
                raise ArithmeticError("Invalid physical row price")
            prices[i] = F(v)
        for j,c in enumerate(cost):
            if sum(p*MATRIX[i][j] for i,p in enumerate(prices))<c:
                raise ArithmeticError(f"Column {j} uncovered by certificate {n+1}")
        margin = target-dot(prices,CAPS)
        if margin < 0:
            raise ArithmeticError("Dual exceeds the requested price")
        print(f"Dual {n+1}: {len(entries)} physical rows, exact margin {margin}.")
    verify_obstruction()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate",action="store_true")
    args = parser.parse_args()
    targets = objectives()
    if args.generate:
        records = generate(targets)
        verify(records,targets)
        CERT.write_text(json.dumps(records,separators=(",",":"))+"\n",encoding="utf-8")
    else:
        verify(json.loads(CERT.read_text(encoding="utf-8")),targets)

