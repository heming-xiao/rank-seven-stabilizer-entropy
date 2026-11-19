"""Exact scalar test for a whole sixth-probability interval at positive shared width."""

from fractions import Fraction as F
from math import isqrt


A = F(101*168,100)
K = F(5,2)
RAYS = [(1,F(0)),(1,F(1,2)),(1,F(2,3)),(1,F(1)),(1,F(2)),(1,F(4)),(0,F(1))]


def sqrt_above(value):
    scale=10**8
    return F(isqrt(value.numerator*scale**2//value.denominator)+1,scale)


def main():
    b,z,y,x = F(11,10),F(9),F(3,4),F(4)
    g=z*x
    delta=y*(z+y+x)
    hstar=g-z-3*x-F(5,2)
    am=1+x+y+z
    limit=min(1+x,1+z/(1+x+y))
    width=am*(1+x)*max(0,1-sqrt_above(b/limit))**2
    r0=y*y*(y*y+(z*z+x*x)/2)
    records=[]
    for left,right in zip(RAYS,RAYS[1:]):
        best=None
        for frac in (F(0),F(1,2),F(1)):
            qf=1+frac**2*72/(z*z+x*x)
            lower_g=max(0,g-(1-frac)*F(200,11)*(b-1)/b)
            for u in (F(1),F(5,4),F(3,2)):
                s=u*lower_g/qf
                lam=24*s/A
                for w in (F(1),F(5,4),F(3,2),F(7,4)):
                    mu=24*w*delta/A
                    highest=(12*w*(2-w)*delta**2+r0)/(K*A)
                    completion=b**3*((z+y+x)*(y+x)*x-lam*(y+2*x)-mu*x)
                    endpoint_margins=[]
                    for c in (F(1),b):
                        gc=g-(1-frac)*F(200,11)*(c-1)/b
                        shared=(g*g/12+s*(2*gc-qf*s))/A
                        rows=[]
                        for n,v in (left,right):
                            P=max(n,v)
                            M=max(n,v/2)
                            Z=max(F(5,2)*n,2*v,2*n+v)
                            if n:
                                trace=n*(1-min(F(1,2),n/(3*v) if v else F(1,2)))
                            else:
                                trace=0
                            # The true highest width is omitted in this example.
                            paid=b*b*(shared*P+highest*v)+96*c*width*trace/A
                            weight=(delta-mu)*(v-(b-1)*(c-1)*max(v,n/2))
                            first=paid-weight+c*(z+2*y+3*x)*M+Z/b**2-c*(g-lam)*n
                            first+=min(b*x,completion*c)*max(0,2*n+v-3*M)/b**2
                            second=paid-weight+c*y*v-c*(hstar-lam)*n
                            rows.append((first,second))
                        endpoint_margins.append(max(min(theta*l+(1-theta)*r for l,r in rows)
                                                    for theta in (F(j,16) for j in range(17))))
                    result=min(endpoint_margins)
                    if best is None or result>best:
                        best=result
        assert best is not None and best>F(1,4),(left,right,best)
        records.append(best)
    print(f"Six adjacent ray pairs, two tail endpoints each; all margins exceed 1/4 (minimum {float(min(records)):.6f}).")


if __name__=="__main__":
    main()
