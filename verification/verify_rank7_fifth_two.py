"""A spectrum-independent rank-six comparison for a fifth probability at least 2d."""

from collections import Counter
from fractions import Fraction as F

from verify_rank7_zero_nominal_payment import A, K, W


def test(box):
    (z, Z), (y, Y), (x, X) = box
    b = F(2)
    g, g_upper = z*x, Z*X
    span, span_upper = z+3*x, Z+3*X
    delta, delta_upper = y*(z+y+x), Y*(Z+Y+X)
    if b*b*delta>F(1800,61) or 5*g_upper<=span+2*y:
        return "earlier domain"
    r = y*y*(y*y+(z*z+x*x)/2)
    highest = (12*W*(2-W)*delta*delta+r)/K
    if b*b*(highest+max(g*g/24,x**4/72))/168+y>(1-W/7)*delta_upper:
        return "weighted split"
    qinv = (z*z+x*x)/(z*z+x*x+72)
    h_upper = g_upper-span-F(5,2)
    for u in (F(1),F(5,4),F(3,4),F(3,2)):
        lam = 24*u*g*qinv/A
        debit = max(0,h_upper-lam)
        theta = max(0,lam-h_upper)/(span_upper+F(5,2))
        shared = (g*g/12+u*(2-u)*g*g*qinv)/A
        if b*shared<debit:
            continue
        tail = min(y-debit,F(9,5)*(y-debit))
        if tail+theta*(span/2+F(2,9))+b*b*(shared+highest/A)>(1-24*W/A)*delta_upper:
            return "rank-six mixed"
    return None


def main():
    # h < 190, k^2 <= Delta < 1800/61 and q < 17, with b >= 2.
    initial=((F(3,5),F(95)),(F(0),F(11,4)),(F(1,5),F(17,2)))
    stack=[(initial,0)]
    counts=Counter()
    max_depth=0
    while stack:
        box,depth=stack.pop()
        result=test(box)
        if result:
            counts[result]+=1
            max_depth=max(max_depth,depth)
            continue
        if depth>=90:
            raise ArithmeticError(f"Unresolved box: {box}")
        j=max(range(3),key=lambda i:(box[i][1]-box[i][0])/(1+box[i][0]))
        lo,hi=box[j]
        mid=(lo+hi)/2
        for part in ((lo,mid),(mid,hi)):
            stack.append((box[:j]+(part,)+box[j+1:],depth+1))
    print(f"Verified {sum(counts.values())} exact leaves, depth {max_depth}: {dict(counts)}")


if __name__=="__main__":
    main()
