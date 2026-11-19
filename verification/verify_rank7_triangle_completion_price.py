"""Exact six-direction example for the triangle and completion criterion."""

from fractions import Fraction as F
from math import isqrt

from verify_rank7_four_equal_tails import EXTERIOR_RATE
from verify_rank7_three_equal_tails import RAYS


def gap_interval(inside, outside):
    if inside <= outside:
        return F(0), F(0)
    scale = 10**12
    product = inside*outside
    root_floor = isqrt(product.numerator*scale**2 // product.denominator)
    root_lo, root_hi = F(root_floor, scale), F(root_floor+1, scale)
    return max(0, inside+outside-2*root_hi), inside+outside-2*root_lo


def margins(use_triangle, upper):
    h, k, q, p, b, c = map(F, ("14.1298", "0.1", "5.82", "0.001", "1.978", "1.955"))
    a = b+p
    x, y, length = h+k+q, k+q, h+2*k+3*q
    alpha, beta, gamma = a+x, a+y, a+q
    g, delta, triangle, cubic = h*q, k*x, y*q, x*y*q
    rate = EXTERIOR_RATE
    loss = b*(c-1)
    rho = min(loss, (gamma-c)*p)
    js = (beta-c)*(gamma-b)-rho
    gain = max(0, g-F(200,11)*(loss-rho))
    j0 = triangle+p*y+(a-c)*q
    s, t = F(5,4)*gain, F(5,4)*delta
    lam, mu = 24*s/rate, 24*t/rate
    c0 = cubic-lam*(y+q)-mu*q
    z = min(j0/13, js, rate*c0/(48*length)) if use_triangle else 0
    payment = c0-24*z*length/rate
    weight = 12*z*(2*j0-13*z)/(40*rate)
    if min(payment, weight, js-z) < 0:
        raise ArithmeticError("Invalid triangle price")
    reserve = (b-c)**2+1
    anti = k*k*(k*k+(h*h+q*q)/2)
    shared_pay = (g*g+12*s*(2*gain-s)+reserve*g*g/(h*h+3*q*q))/(12*rate)
    first_pay = (anti+12*t*(2*delta-t)+reserve*k*k/2)/(F(5,2)*rate)
    hi = int(upper)
    cut1 = gap_interval(alpha*beta*c, alpha*gamma*a*b)[hi]
    cut2 = gap_interval(alpha*gamma*c, max(alpha*a*b*c,beta*gamma*a*b))[hi]
    trace = max(0,a*cubic-delta/3)/(c*g+2*a*cubic)
    out = []
    for n, v in RAYS:
        m, peak = max(n,F(v)/2), max(n,v)
        count = max(F(5,2)*n,2*v,2*n+v)
        extra = max(0,2*n+v-3*m)
        combined = min(q*extra+weight*peak, payment*b*extra+weight*(peak-extra), payment*b*peak)
        exterior = (length*p*(a-c)*(a-1)+p**4+2*(g-lam)*p*p
                    +(delta-mu)*p*(a-c)+3*triangle*p*p+payment*p)
        margin = b*c*length*m+count+exterior*peak+combined
        margin += (delta-mu)*(b-1)*(c-1)*max(v,F(n)/2)
        margin += shared_pay*peak+first_pay*v+(64*v*cut1+96*n*cut2*trace)/rate
        margin -= (g-lam)*c*n+(delta-mu)*v
        out.append(margin)
    return out


def main():
    earlier = min(margins(False, True))
    current = min(margins(True, False))
    if not earlier < -F(1,125) or not current > F(7,50):
        raise ArithmeticError("Exact old and new margin brackets did not pass")
    print("Earlier margin < -1/125; all six triangle-completion margins > 7/50.")


if __name__ == "__main__":
    main()

