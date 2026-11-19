"""Verify uniform forward packing and the single-cut spectral test using exact arithmetic."""
from fractions import Fraction as F
from itertools import product
from math import isqrt, floor
import argparse
import json
from pathlib import Path

from verify_rank7_forward_coefficients import (
    TRIPLES, UNIVERSE, KNOWN_ROWS, REFERENCE, coefficient_table, row_table, verify_dual,
)


WEDGES = [UNIVERSE.difference(t) for t in TRIPLES]
ROWS = row_table()[:len(KNOWN_ROWS)]
CAPS = [r[2] for r in KNOWN_ROWS]
REF = [int(t in REFERENCE) for t in TRIPLES]
CERT = (Path(__file__).resolve().parents[1] / "certificates" / "rank7" / "rank7_uniform_cut_packing.json")
RAYS = ((1,0),(1,F(1,2)),(1,1),(1,2),(1,4),(0,1))


def cell_costs():
    forward = coefficient_table()
    uncoupled = {}
    adjusted = {}
    su, sy = [dict((m,[0]*35) for m in forward) for _ in range(2)]
    for pos,wedge in enumerate(WEDGES):
        for pair in (frozenset((0,1)), frozenset((0,2))):
            if pair <= wedge:
                i,j = sorted(wedge - pair)
                for left,right in product(range(i,7), range(j,7)):
                    su[tuple(sorted((0,2,left,right)))][pos] += 1
                    if 1 in pair:
                        for g1,g2 in ((0,1),(1,1),(1,2)):
                            sy[tuple(sorted((g1,g2,left,right)))][pos] += 1
    for m,base in forward.items():
        if not {3,4,5}.intersection(m):
            continue
        key = "".join(map(str,m))
        if not any(su[m]) and not any(sy[m]):
            uncoupled[key] = base
            continue
        for first,second in product((0,F(1,2)), repeat=2):
            costs = []
            for pos,w in enumerate(WEDGES):
                shared = int({0,1}<=w)+int({0,2}<=w)
                correction = (1-first)*shared if m==(0,2,5,6) else 0
                costs.append(base[pos]-first*su[m][pos]-second*sy[m][pos]-correction)
            adjusted[f"{key}_{int(2*first)}{int(2*second)}"] = costs
    return uncoupled, adjusted


def block_costs():
    costs = {}
    for j,w in enumerate(WEDGES):
        high = [int(i in w) for i in range(3)]
        N = 1
        v = int({0,1}<=w)
        shared = v + int({0,2}<=w)
        A = int({0,1,2}<=w)
        for level in range(1,4):
            T = sum(high[:level])
            for label,price in (("zero",0),("shared",level*shared),("highest",F(level,2)*v)):
                costs.setdefault(f"T{level}_{label}",[]).append(T+price)
        costs.setdefault("TH_cross",[]).append(sum(high)+2*shared+v+A)
        for label,price in (("zero",0),("shared",F(5,2)*shared),("highest",2*v),("cross",2*shared+v)):
            costs.setdefault("N_"+label,[]).append(N+price)
        costs.setdefault("head_pairs",[]).append(shared+int({1,2}<=w))
        # Nonnegative tail-only 0-wedges can be omitted from the 4 directed rows.
        costs.setdefault("two_shared_plus_x",[]).append(2*shared-A)
    return costs


def unrounded_prices(cost):
    from scipy.optimize import linprog
    import numpy as np
    sol = linprog(-np.array(cost,dtype=float), A_ub=ROWS,b_ub=CAPS,bounds=(0,None))
    if not sol.success:
        raise ArithmeticError(sol.message)
    prices = [F(float(-p)).limit_denominator(1000000) for p in sol.ineqlin.marginals]
    return [[i,str(p)] for i,p in enumerate(prices) if p]


def check_prices(key,prices,cost,expected):
    if verify_dual(prices,ROWS,CAPS,cost) != expected:
        raise ArithmeticError(f"Wrong objective for {key}")


def verify(record, unadjusted, adjusted, blocks):
    source = (Path(__file__).resolve().parents[1] / "certificates" / "rank7" / "rank7_forward_coefficients.json")
    original = {tuple(row["monomial"]):row["prices"]
                for row in json.loads(source.read_text(encoding="utf-8"))["old_certificates"]}
    for key,cost in unadjusted.items():
        prices = original[tuple(map(int,key))]
        check_prices(key,prices,cost,sum(v*r for v,r in zip(cost,REF)))
    if set(record)!=set(adjusted)|set(blocks):
        raise ArithmeticError("Incomplete adjusted or geometric certificate")
    for key,cost in {**adjusted,**blocks}.items():
        # 2 nu + x <= 1 has reference slack one; its raw cost is 2*Lshared-A.
        expected = 8 if key=="two_shared_plus_x" else sum(v*r for v,r in zip(cost,REF))
        check_prices(key,record[key],cost,expected)
    print(f"{len(unadjusted)} original tail coefficients, {len(adjusted)} weighted-corner and "
          f"{len(blocks)} geometric certificates verified with rational prices.")


def rational_sqrt_bounds(x, scale=10**8):
    m = isqrt(floor(x*scale**2))
    lower = F(m,scale)
    return lower, lower if lower**2==x else F(m+1,scale)


def price_test(t):
    alpha,beta,gamma,a,b,c,d=t
    h,k,q=alpha-beta,beta-gamma,gamma-a
    m=alpha-a
    g,delta=h*q,k*m
    rho=k**2*(k**2+(h**2+q**2)/2)
    G=g-F(200,11)*b*(c-d)
    if not (g>0 and G>=0 and gamma*d>a*b and alpha*c*d>beta*a*b):
        raise ValueError("Outside the reported example's branch")
    lam,mu=G/7,delta/7
    A,B,F0=g*c*d,delta*d*d,a*m*(k+q)*q
    omega=max(0,(F0-B/3)/(A+2*F0))
    inside=alpha*gamma*c*d
    outside=max(alpha*a*b*c,beta*gamma*a*b)
    gap=max(0,rational_sqrt_bounds(inside)[0]-rational_sqrt_bounds(outside)[1])**2
    compression=F(4,7)*gap*omega
    shared=(12*G**2+g**2)/(12*168)
    highest=(12*delta**2+rho)/(F(5,2)*168)
    D=d*(m*(k+q)*q-lam*(k+2*q)-mu*q)
    qweight=d**3*q
    theta=min(1,D/qweight) if qweight else 0
    margins=[]
    for n,r in RAYS:
        n,r=F(n),F(r)
        M=max(n,r/2)
        z=max(5*n/2,2*r,2*n+r)
        head=3*M+theta*max(0,2*n+r-3*M)
        supply=(d**3*((h+2*k)*M+q*head)+d**4*z
                +shared*max(n,r)+highest*r+compression*n)
        cost=(g-lam)*c*d*n+(delta-mu)*d**2*r
        margins.append(supply-cost)
    return margins


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate",action="store_true")
    args=parser.parse_args()
    ordinary, weighted=cell_costs()
    blocks=block_costs()
    if args.generate:
        data={key:unrounded_prices(cost) for key,cost in {**weighted,**blocks}.items()}
        verify(data,ordinary,weighted,blocks)
        CERT.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8")
    else:
        verify(json.loads(CERT.read_text(encoding="utf-8")),ordinary,weighted,blocks)
    regression=tuple(map(F,("19.32","4.69","4.13","1.012","1.008","1.004","1")))
    margins=price_test(regression)
    if min(margins)<=F(3,2):
        raise ArithmeticError(f"Insufficient regression ray margins {margins}")
    print("Each of the six rational lower margins at the strictly ordered regression exceeds 3/2.")
    second=tuple(map(F,("15","4.2","4","1.03","1.02","1.01","1")))
    if min(price_test(second))<=F(29,10):
        raise ArithmeticError("The second example misses its claimed ray margin")
    print("Each of the six exact lower margins at (15,4.2,4,1.03,1.02,1.01,1) exceeds 29/10.")

