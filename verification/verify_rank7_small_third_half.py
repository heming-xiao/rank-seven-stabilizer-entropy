"""Exact rank-seven cover at q <= b/2, with separate fourth-gap branches."""

from collections import Counter
from fractions import Fraction as F
import sys

from verify_rank7_zero_nominal_payment import A, K, W


RAYS = [(F(1),F(0)),(F(1),F(1,2)),(F(1),F(1)),(F(1),F(2)),(F(1),F(4)),(F(0),F(1))]
GAP = F(1,16)
INITIAL = ((F(3,5),F(22)),(F(0),F(11,2)),(F(1,5),F(1,2)))


def certify(box, low, high, branch):
    (z,Z),(y,Y),(x,X) = box
    span = z+2*y+3*x
    g, g_hi = z*x,Z*X
    delta, delta_hi = y*(z+y+x),Y*(Z+Y+X)
    if low >= 1+X or 5*g_hi <= span or low**2*(z+4*y+3*x) >= 22:
        return "previous theorem"
    if low**2*delta > F(1800,61):
        return "previous theorem"
    r = y*y*(y*y+(z*z+x*x)/2)
    highest = (12*W*(2-W)*delta**2+r)/K
    if low**2*(highest+max(g*g/24,x**4/72))/168+y>(1-W/7)*delta_hi:
        return "weighted split"
    # C/b^3=x(z+y+x)(x+(1-24w/A)y), with positive factors.
    rho = 1-24*W/A
    comp = x*(z+y+x)*(x+rho*y)
    geom = min(x/high,low*comp)
    shared_price = low**2*g*g/(12*A)
    high_price = low**2*highest/A-rho*delta_hi
    extra = 0
    if branch == "large":
        extra = GAP*low*comp
    else:
        pmax = F(0) if branch=="tied" else GAP
        product = high*(high+pmax)
        diff = max(0, y-(product-1)*(1+X)-pmax*product/low)
        width = (1+x+y+z)*diff**2/((1+high+pmax/2)**2*(1+X+Y+pmax/low))
        high_price += 64*width/A
    for n,v in RAYS:
        P=max(n,v)
        M=max(n,v/2)
        floor=max(F(5,2)*n,2*v,2*n+v)
        # Combine z terms before enclosing. M-x*n >= n/2 on this domain.
        singleton=z*(M-X*n)+(2*y+3*x)*M
        margin = (shared_price+extra)*P+high_price*v+singleton
        margin += floor/high**2 + geom*max(0,2*n+v-3*M)
        if margin <= 0:
            return None
    return "highest mixed"


def main(branch):
    if branch not in ("tied","small","large"):
        raise ValueError("Choose tied, small or large")
    total=0
    depth_max=0
    cumulative=Counter()
    for j in range(8):
        low,high=1+F(j,16),1+F(j+1,16)
        stack=[(INITIAL,0)]
        counts=Counter()
        while stack:
            box,depth=stack.pop()
            result=certify(box,low,high,branch)
            if result:
                counts[result]+=1
                depth_max=max(depth_max,depth)
                continue
            if depth>=80:
                raise ArithmeticError(f"Unresolved {branch}, slab {low},{high} box {box}")
            index=max(range(3),key=lambda i:(box[i][1]-box[i][0])/(1+box[i][0]))
            lo,hi=box[index]
            mid=(lo+hi)/2
            for part in ((lo,mid),(mid,hi)):
                stack.append((box[:index]+(part,)+box[index+1:],depth+1))
        total+=sum(counts.values())
        cumulative.update(counts)
        print(f"{branch} slab {j+1}: {sum(counts.values())} leaves",flush=True)
    print(f"{branch}: verified {total} leaves, max depth {depth_max}, {dict(cumulative)}",flush=True)


if __name__=="__main__":
    main(sys.argv[1])
