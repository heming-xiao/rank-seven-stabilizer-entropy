"""Exact common-frame three-price packing. Verification uses only the standard library."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from verify_rank7_forward_coefficients import (
    KNOWN_ROWS, REFERENCE, TRIPLES, UNIVERSE, coefficient_table, row_table, verify_dual,
)


def const(x):
    return {():x} if x else {}


def var(i):
    return {(i,):1}


def plus(*polys):
    total=Counter()
    for poly in polys:
        total.update(poly)
    return {m:c for m,c in total.items() if c}


def times(*polys):
    out=const(1)
    for poly in polys:
        nxt=Counter()
        for m,c in out.items():
            for n,v in poly.items():
                nxt[tuple(sorted(m+n))]+=c*v
        out={m:c for m,c in nxt.items() if c}
    return out


def neg(p):
    return {m:-c for m,c in p.items()}


def minus(p,q):
    return plus(p,neg(q))


def scaled(k,p):
    return times(const(k),p)


def require_same(left,right,context):
    if minus(left,right):
        raise ArithmeticError(f"Polynomial identity fails: {context}")


def test_identities():
    # Variables are the three head increments X,Y,Z and the four actual tails a,b,c,d.
    X,Y,Z,a,b,c,d=[var(i) for i in range(7)]
    inc=(X,Y,Z)
    full=[plus(a,v) for v in inc]+[a,b,c,d]
    base=[a,a,a,a,b,c,d]
    g=times(minus(X,Y),Z)
    delta=times(minus(Y,Z),X)
    J=times(Y,Z)
    tri_product=times(X,Y,Z)
    third_sum=plus(X,Y,Z)
    gain_terms=plus(times(g,plus(Y,Z)),times(delta,Z),times(J,third_sum))
    require_same(gain_terms,scaled(3,tri_product),"Euler identity for balanced prices")
    ref_w=[UNIVERSE.difference(t) for t in TRIPLES if t in REFERENCE]
    for triple in TRIPLES:
        w=UNIVERSE.difference(triple)
        heads=frozenset((0,1,2))
        tails=tuple(range(3,7))
        pairs=(frozenset((0,1)),frozenset((0,2)),frozenset((1,2)))
        Ii=[int({0,1,2,i}<=w) for i in tails]
        delta_A_price=neg(plus(*(scaled(v,base[i]) for v,i in zip(Ii,tails))))
        K={}
        C12={}
        for i,j in combinations(tails,2):
            Wij=sum(int(e.union((i,j))<=w) for e in pairs)
            K[i,j]=-Ii[i-3]-Ii[j-3]-Wij
            C12[i,j]=int({1,2,i,j}<=w)
        selection=[]
        for spec in (base,full):
            u=[]
            for e in pairs:
                u.append(times(*(spec[i] for i in w-e)) if e<=w else {})
            selection.append((u[0],plus(*u[:2]),plus(*u)))
        (Y0,U0,T0),(Yfull,Ufull,Tfull)=selection
        for label,target,old,shift in (
            ("highest",Yfull,Y0,Z),("shared",Ufull,U0,plus(Y,Z)),
            ("triangle",Tfull,T0,third_sum),
        ):
            require_same(target,minus(old,times(shift,delta_A_price)),(label,triple))
        low=times(*(base[i] for i in w))
        for i in w & heads:
            low=plus(low,times(inc[i],*(base[j] for j in w-{i})))
        expected=plus(low,times(g,U0),times(delta,Y0),times(J,T0),neg(times(tri_product,delta_A_price)))
        require_same(times(*(full[i] for i in w)),expected,("complete head expansion",triple))

        # All subsequent expressions are coefficients of w_I - w_I^*. Positive
        # uncentered A_i terms have zero weight on the sole reference completion 3.
        Nshare=sum(int(e<=w) for e in pairs[:2])
        Ntri=sum(int(e<=w) for e in pairs)
        gap_x=neg(const(sum(Ii)))
        coeff_x=plus(times(a,minus(a,b)),times(minus(a,c),minus(a,d)))
        fl_shared=[times(minus(a,base[i]),minus(plus(scaled(2,a),base[i]),plus(b,c,d))) for i in tails]
        shared_loss=plus(
            *(scaled(K[i,j]+C12[i,j],minus(times(base[i],base[j]),times(c,d))) for i,j in combinations(tails,2)),
            times(coeff_x,gap_x),*(scaled(v,weight) for v,weight in zip(Ii,fl_shared)))
        require_same(minus(scaled(Nshare,times(c,d)),U0),shared_loss,("six-row shared identity",triple))
        fl_tri=[times(base[i],minus(a,base[i])) for i in tails]
        tri_loss=plus(
            *(scaled(K[i,j],minus(times(base[i],base[j]),times(d,d))) for i,j in combinations(tails,2)),
            times(minus(scaled(3,a),plus(b,c,d)),delta_A_price),
            *(scaled(v,weight) for v,weight in zip(Ii,fl_tri)))
        require_same(minus(scaled(Ntri,times(d,d)),T0),tri_loss,("six-row triangle identity",triple))

    # The uncentered terms translated to the centered column identities above
    # have zero reference corrections exactly as used in the proof.
    ref_sets={frozenset(w) for w in ref_w}
    if [int(frozenset((0,1,2,i)) in ref_sets) for i in range(3,7)]!=[1,0,0,0]:
        raise ArithmeticError("Incorrect reference triple completion")
    if [p for p in combinations(range(3,7),2) if frozenset((1,2,*p)) in ref_sets]!=[(5,6)]:
        raise ArithmeticError("Incorrect reference pair-12 tail completion")
    swap=(0,1,6,3,4,5,2)
    permuted={frozenset(swap[i] for i in w) for w in ref_sets}
    if any({0,1,2}<=w for w in permuted):
        raise ArithmeticError("The three-head completion of the swapped Fano frame should vanish")
    if len(permuted)!=7 or any(sum(i in w for w in permuted)!=4 for i in range(7)):
        raise ArithmeticError("Incorrect total or singleton on the swapped Fano frame")
    for pair in combinations(range(7),2):
        if sum(set(pair)<=w for w in permuted)!=2:
            raise ArithmeticError("Incorrect pair count on the swapped Fano frame")


def test_low_forward():
    source=(Path(__file__).resolve().parents[1] / "certificates" / "rank7" / "rank7_forward_coefficients.json")
    original={tuple(row["monomial"]):row["prices"]
              for row in json.loads(source.read_text(encoding="utf-8"))["old_certificates"]}
    matrix=row_table()[:len(KNOWN_ROWS)]
    caps=[row[2] for row in KNOWN_ROWS]
    count=0
    for monomial,cost in coefficient_table().items():
        if sum(i<=2 for i in monomial)>1 or not set(monomial)&{3,4,5}:
            continue
        reference=sum(value for value,tri in zip(cost,TRIPLES) if tri in REFERENCE)
        if verify_dual(original[monomial],matrix,caps,cost)!=reference:
            raise ArithmeticError(f"Uncertified low-head quartic {monomial}")
        count+=1
    return count


if __name__=="__main__":
    test_identities()
    print("Verified exact head expansion and two six-row loss identities in all 35 columns.")
    print(f"Verified {test_low_forward()} ordinary quartics for the constant and single-head tail terms.")
    print("Balanced common rates g/7, Delta/7 and J/7 retain (4/7)XYZ of the completion price.")
    print("The physical 2/6 swap is sharp for the signed completion charge on all flat tails.")

