"""Exact 3-D cover for the simultaneous zero-nominal-width comparison."""

from collections import Counter
from fractions import Fraction as F
from math import prod


A = F(101 * 168, 100)
K = F(5, 2)
W = F(5, 4)
EXTRA_TAIL = F(0)
INITIAL = ((F(3, 5), F(50)), (F(0), F(11, 2)), (F(1, 5), F(17)))


def certificate(box):
    (z, Z), (y, Y), (x, X) = box
    g, G = z*x, Z*X
    span, span_hi = z+3*x, Z+3*X
    delta, delta_hi = y*(z+y+x), Y*(Z+Y+X)
    b = 1+max(y/(1+X+EXTRA_TAIL), z/(1+X+Y+EXTRA_TAIL))
    if b>3 or b*b*delta>F(1800, 61) or 5*G <= span+2*y:
        return "domain"
    r = y*y*(y*y+(z*z+x*x)/2)
    highest = (12*W*(2-W)*delta*delta+r)/K
    transfer = b*b*(highest+max(g*g/24,x**4/72))/168+y-(1-W/7)*delta_hi
    if transfer>0:
        return "weighted split"
    # inv_q is the lower bound on 1/[1+72/(z^2+x^2)].
    s2 = z*z+x*x
    inv_q = s2/(s2+72)
    h_hi = G-span-F(5, 2)
    for u in (F(1), F(5, 4), F(3, 4), F(3, 2)):
        lam = (24/A)*u*g*inv_q
        residual_hi = max(0, h_hi-lam)
        theta = max(0, lam-h_hi)/(span_hi+F(5, 2))
        shared = (g*g/12+u*(2-u)*g*g*inv_q)/A
        if b*shared < residual_hi:
            continue
        net = y-residual_hi
        tail = min(net,F(9,5)*net)
        highest_margin = (tail+theta*(span/2+F(2,9))
                          +b*b*(shared+highest/A)-(1-24*W/A)*delta_hi)
        if highest_margin>0:
            return "joint mixed"
    return None


def main():
    stack = [(INITIAL,0)]
    counts = Counter()
    max_depth = 0
    while stack:
        box, depth = stack.pop()
        result = certificate(box)
        if result is not None:
            counts[result] += 1
            max_depth = max(max_depth,depth)
            continue
        if depth >= 84:
            raise ArithmeticError(f"Unresolved exact box at depth {depth}: {box}")
        # Select the largest log-relative spread using rational comparisons.
        j = max(range(3),key=lambda i: (box[i][1]-box[i][0])/(1+box[i][0]))
        lo, hi = box[j]
        mid = (lo+hi)/2
        for part in ((lo,mid),(mid,hi)):
            stack.append((box[:j]+(part,)+box[j+1:],depth+1))
    print(f"Verified {sum(counts.values())} exact boxes at maximum depth {max_depth}: {dict(counts)}")


if __name__ == "__main__":
    main()
