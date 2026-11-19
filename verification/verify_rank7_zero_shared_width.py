"""Exact four-slab cover when only the shared nominal width vanishes."""

from collections import Counter
from fractions import Fraction as F
import sys

from verify_rank7_zero_nominal_payment import A, INITIAL, K, W


SLABS = [(F(1), F(5, 4)), (F(5, 4), F(3, 2)), (F(3, 2), F(2)), (F(2), F(3))]


def certify(box, slab, branch):
    (z, Z), (y, Y), (x, X) = box
    base, top = slab
    # Any remaining actual frame has p < 5/7; only alpha <= b*beta is imposed.
    if branch.startswith("head"):
        b = max(base, 1+z/(1+X+Y+F(5, 7)/base))
        p_lower = F(0) if branch == "head" else b*max(0,z/(top-1)-1-X-Y)
    else:
        b = max(base, 1+x/(1+F(5, 7)/base))
        # gamma <= ab and b <= top force an absolute fourth gap.
        p_lower = b*max(0,x/(top-1)-1)
    g, G = z*x, Z*X
    span, span_hi = z+3*x, Z+3*X
    delta, delta_hi = y*(z+y+x), Y*(Z+Y+X)
    if b>top or b*b*delta>F(1800, 61) or 5*G<=span+2*y:
        return "domain"
    if branch != "head" and (X <= F(1, 2) or Z <= F(3, 2)) and b*b*(z+4*y+3*x) >= 22:
        return "head-gap theorem"
    r = y*y*(y*y+(z*z+x*x)/2)
    highest = (12*W*(2-W)*delta*delta+r)/K
    discount = max(0,1-p_lower*p_lower)
    transfer = b*b*(highest+max(g*g/24,x**4/72))/168+y-(1-W/7)*delta_hi*discount
    if transfer>0:
        return "weighted split"
    s2 = z*z+x*x
    inv_q = s2/(s2+72)
    h_hi = G-span-F(5, 2)
    for u in (F(1), F(5, 4), F(3, 4), F(3, 2)):
        lam = (24/A)*u*g*inv_q
        residual = max(0, h_hi-lam)
        theta = max(0, lam-h_hi)/(span_hi+F(5, 2))
        shared = (g*g/12+u*(2-u)*g*g*inv_q)/A
        if b*shared < residual:
            continue
        net = y-residual
        tail = min(net,min(F(9, 5),top)*net)
        margin = (tail+theta*(span/2+2/top**2)+b*b*(shared+highest/A)
                  -(1-24*W/A)*delta_hi*discount)
        if margin>0:
            return "joint mixed"
    return None


def main(branch):
    grand = 0
    if branch == "head":
        slabs = SLABS
        initial = INITIAL
    elif branch in ("head-fine","tail"):
        slabs = [(1+F(j,8),1+F(j+1,8)) for j in range(16)]
        initial = INITIAL if branch == "head-fine" else ((F(3,5),F(190)),(F(0),F(11,2)),(F(1,5),F(17)))
    else:
        raise ValueError("Choose head or tail")
    for slab in slabs:
        counts = Counter()
        stack = [(initial,0)]
        max_depth = 0
        while stack:
            box, depth = stack.pop()
            result = certify(box,slab,branch)
            if result:
                counts[result] += 1
                max_depth = max(max_depth,depth)
                continue
            if depth >= 90:
                raise ArithmeticError(f"Unresolved box in {slab} at depth {depth}: {box}")
            j = max(range(3),key=lambda i: (box[i][1]-box[i][0])/(1+box[i][0]))
            lo, hi = box[j]
            mid = (lo+hi)/2
            for part in ((lo,mid),(mid,hi)):
                stack.append((box[:j]+(part,)+box[j+1:],depth+1))
        grand += sum(counts.values())
        print(f"b in {slab}: {sum(counts.values())} leaves, depth {max_depth}, {dict(counts)}",flush=True)
    print(f"All {grand} exact leaves verified.",flush=True)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "head")
