"""Check simultaneous true-cut trace prices on a rational spectrum."""

from fractions import Fraction as F

from verify_rank7_fifth_gap_compression import square_root_enclosure
from verify_rank7_monotone_fifth_gap import RATE, RAYS, score


def width_enclosure(inside, outside):
    inside_lo, inside_hi = square_root_enclosure(inside)
    outside_lo, outside_hi = square_root_enclosure(outside)
    return max(inside_lo-outside_hi, 0)**2, max(inside_hi-outside_lo, 0)**2


def trace_prices(n, v):
    if n == 0:
        return 2*F(v)/3, F(0)
    ratio = F(v)/n
    limit = min(F(1, 2), 1/(3*ratio)) if ratio else F(1, 2)
    return v*(1-ratio*limit), n*(1-limit)


def verify():
    gaps = tuple(map(F, ("14.08", ".95", "4.01", ".01", "1.05")))
    h, k, q, p, c = gaps
    tail_gap = F(3, 100)
    b, a = c+tail_gap, c+tail_gap+p
    x, y = h+k+q, k+q
    alpha, beta, gamma = a+x, a+y, a+q
    highest = width_enclosure(alpha*beta*c, alpha*gamma*a*b)
    shared = width_enclosure(alpha*gamma*c, max(alpha*a*b*c, beta*gamma*a*b))
    assert highest[0] > 0 and shared[0] > 0
    cubic = a*x*y*q
    omega = max(cubic-k*x/3, 0)/(c*h*q+2*cubic)
    assert 0 < omega < F(1, 2)
    old = [score(gaps, tail_gap, n, v)+(64*v*highest[1]+96*n*omega*shared[1])/RATE
           for n, v in RAYS]
    assert min(old) < -F(2, 5)
    for n, v in (*RAYS, (1, F(2, 3))):
        highest_trace, shared_trace = trace_prices(n, v)
        assert highest_trace >= 2*F(v)/3 and shared_trace >= F(n)/2
        improved = (score(gaps, tail_gap, n, v)
                    +96*(highest_trace*highest[0]+shared_trace*shared[0])/RATE)
        assert improved > max(F(n), F(v)/2)
    print("Joint trace prices and the strict seven-ray example verified exactly.")


if __name__ == "__main__":
    verify()

