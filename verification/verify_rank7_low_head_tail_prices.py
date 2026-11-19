"""Exact tail-weighted packing coefficients and no-gap pure exterior region."""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json
from math import prod
from pathlib import Path

from verify_rank7_forward_coefficients import (
    KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE, coefficient_table, row_table, verify_dual,
)


ROWS=row_table()[:len(KNOWN_ROWS)]
CAPS=[row[2] for row in KNOWN_ROWS]
WEDGES=[UNIVERSE.difference(triple) for triple in TRIPLES]
REF=[int(triple in REFERENCE) for triple in TRIPLES]
HIGHEST=[int({0,1}<=w) for w in WEDGES]
SHARED=[int({0,1}<=w)+int({0,2}<=w) for w in WEDGES]
TOP=[int(w=={0,1,2,3}) for w in WEDGES]
CERT=(Path(__file__).resolve().parents[1] / "certificates" / "rank7" / "rank7_low_head_tail_prices.json")


def polynomial(indices):
    costs=Counter()
    for term in product(*(range(i,7) for i in indices)):
        costs[tuple(sorted(term))]+=1
    return costs


def targets():
    table=coefficient_table()
    bcd=polynomial((4,5,6))
    # If p=b_3, t=b_4 and e=b_5, the product is p(p+t)(p+t+e).
    cluster=Counter(tuple(sorted((3,i,j))) for i in (3,4) for j in (3,4,5))
    if set(bcd)&set(cluster):
        raise ArithmeticError("Tail factors double counted")
    out={}
    for i in range(3):
        for monomials,rate in ((bcd,F(1,2)),(cluster,F(1))):
            for tail,coeff in monomials.items():
                m=(i,*tail)
                key="".join(map(str,m))
                base=table[m]
                for probe,price,counts in (("v",rate,HIGHEST),("nu",F(1),SHARED)):
                    out[key+"_"+probe]=[c+(i+1)*coeff*price*p for c,p in zip(base,counts)]
    if len(out)!=60:
        raise ArithmeticError("Incomplete set of coupon coefficients")
    return out


def verify_top_wedge():
    row_index={key:i for i,key in enumerate(KNOWN_ROWS)}
    for counts,keys,cap in (
        (HIGHEST, [("four_set",(2,4,5,6),1),("four_set",(3,4,5,6),1),("pair",(2,3),1)],3),
        (SHARED, [("directed_link",(3,0),2),("pair",(4,5),1),
                  ("pair",(4,6),1),("pair",(5,6),1)],5),
    ):
        objective=[x+y for x,y in zip(TOP,counts)]
        if verify_dual([[row_index[key],"1"] for key in keys],ROWS,CAPS,objective)!=cap:
            raise ArithmeticError("Missing top-wedge deficit price")
    table=coefficient_table()
    # Only the top wedge can supply four small forward indices. Its product
    # is (alpha-b)(beta-b)(gamma-b)(a-b), including exactly S*(a-b)^3
    # from the three singleton-head cubic-cluster coupons.
    for m,cost in table.items():
        if max(m)>3:
            continue
        for j,v in enumerate(cost):
            if not TOP[j] and v:
                raise ArithmeticError("Top-four price contains an outside wedge")
        if m[0]<3 and m[1:]==(3,3,3):
            if sum(v for v,f in zip(cost,TOP) if f)!=m[0]+1:
                raise ArithmeticError("Incorrect correction for the overlapping head coupon")


def generate(goals):
    from scipy.optimize import linprog
    out={}
    for key,cost in goals.items():
        sol=linprog([-float(c) for c in cost],A_ub=ROWS,b_ub=CAPS,bounds=(0,None))
        if not sol.success:
            raise ArithmeticError(sol.message)
        y=[F(float(-v)).limit_denominator(100000) for v in sol.ineqlin.marginals]
        out[key]=[[i,str(v)] for i,v in enumerate(y) if v]
    return out


def verify(goals,record):
    if set(record)!=set(goals):
        raise ArithmeticError("Incorrect coefficient set")
    raw=coefficient_table()
    ordinary={tuple(row["monomial"]):row["prices"] for row in
              json.loads(CERT.with_name("rank7_forward_coefficients.json").read_text(encoding="utf-8"))["old_certificates"]}
    for key,cost in goals.items():
        if verify_dual(record[key],ROWS,CAPS,cost)!=sum(v*f for v,f in zip(cost,REF)):
            raise ArithmeticError(f"Dual fails on {key}")
        m=tuple(map(int,key.split("_")[0]))
        if verify_dual(ordinary[m],ROWS,CAPS,raw[m])!=sum(v*f for v,f in zip(raw[m],REF)):
            raise ArithmeticError(f"Missing zero-price option for {m}")
    verify_top_wedge()
    print("60 tail-weighted duals, all zero-price options, and both top-wedge rows verified exactly.")


def interval_demo():
    # The unbounded six-parameter box in the note has alpha>=20. The other
    # endpoints below are exact extrema or upper bounds on this box.
    qmax=F("4.1")-F("2.9")
    kmax=F("8")-F("3.9")
    combined=qmax+2*F(".1")*kmax/F("1.4")
    if combined>=F("1.9") or F("4.1")*F(".1")>=F("2.9")*F("1.9"):
        raise ArithmeticError("No-gap unbounded box failed")
    if F("8")*F("1.6")*F(".1")>=F("3.9")*F("2.9")*F("1.9"):
        raise ArithmeticError("The individual highest-pair amplitude separation could be positive")
    if F("3.1")*(F(1,20)+F(1,7))>=1 or 20<=3*F("2.1"):
        raise ArithmeticError("Original elementary inverse or spread criteria could apply")
    # A distinct collar where q exceeds b, so the simple unbounded cone fails.
    alpha,beta,gamma,a,b,c,d=map(F,("22","8","7","3","2","1.5",".1"))
    h,k,q=alpha-beta,beta-gamma,gamma-a
    A=c*d*h*q
    B=d*d*k*(alpha-a)
    D4=prod(t-b for t in (alpha,beta,gamma,a))
    if not (q>b and gamma*d<a*b and A+B<D4):
        raise ArithmeticError("Independent explicit floor collar failed")
    print(f"Unbounded strictly ordered box: q+2dk/c <= {combined} < 19/10.")
    print(f"At the separate q>b point: A+B = {A+B}, D4 = {D4}.")


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate",action="store_true")
    args=parser.parse_args()
    goals=targets()
    if args.generate:
        data=generate(goals)
        verify(goals,data)
        CERT.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8")
    else:
        verify(goals,json.loads(CERT.read_text(encoding="utf-8")))
    interval_demo()

