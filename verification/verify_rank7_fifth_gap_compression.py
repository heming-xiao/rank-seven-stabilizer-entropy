"""Exact two-cut fifth-gap comparison using a quadratic lower envelope."""

from fractions import Fraction as F
from math import isqrt, prod

from verify_rank7_monotone_fifth_gap import MATCHING_PRICE, RATE, RAYS, score


def square_root_enclosure(value):
    scale = 10**12
    scaled_square = value * scale**2
    lower = F(isqrt(scaled_square.numerator // scaled_square.denominator), scale)
    return lower, lower if lower**2 == value else lower + F(1, scale)


def endpoint_bounds(gaps, upper_gap):
    h, k, q, p, c = gaps
    a, b = c+p, c
    gamma, beta, alpha = a+q, a+q+k, a+q+k+h
    # Each row records the fixed inner multiplier, its varying factor,
    # the starting prefactor, and the factors of the outer radicand.
    rows = ((beta, alpha, (gamma, a, b)),
            (gamma, alpha, (c, a, b)),
            (alpha, gamma, (beta, a, b)))
    endpoints = []
    for index, (inner, prefactor, factors) in enumerate(rows):
        inner_low, _ = square_root_enclosure(c*inner)
        _, outer_high = square_root_enclosure(prod(factors))
        difference = max(0, inner_low-outer_high)
        if index == 1:
            slope_outer = outer_high*(1/a+1/b)/2
        else:
            values = tuple(factor+upper_gap for factor in factors)
            _, outer_at_end = square_root_enclosure(prod(values))
            slope_outer = outer_at_end*sum(1/value for value in values)/2
        _, inner_at_end = square_root_enclosure(c*(inner+upper_gap))
        slope = max(0, slope_outer-c/(2*inner_at_end))
        endpoints.append((prefactor, difference, slope))
    hq = h*q
    x, y = h+k+q, k+q
    delta, cubic = k*x, x*y*q
    omega = max(a*cubic-delta/3, 0)/(c*hq+2*a*cubic)
    return endpoints, omega


def minimum_on_interval(constant, slope, terms, upper):
    breakpoints = sorted({F(0), upper, *(offset/rate for _, offset, rate in terms
                                         if rate > 0 and 0 < offset/rate < upper)})
    candidates = set(breakpoints)
    for left, right in zip(breakpoints, breakpoints[1:]):
        midpoint = (left+right)/2
        active = [(weight, offset, rate) for weight, offset, rate in terms
                  if offset > rate*midpoint]
        quadratic = sum(weight*rate**2 for weight, _, rate in active)
        linear = slope-2*sum(weight*offset*rate for weight, offset, rate in active)
        if quadratic > 0 and left < -linear/(2*quadratic) < right:
            candidates.add(-linear/(2*quadratic))
    return min(constant+slope*gap+sum(weight*max(offset-rate*gap, 0)**2
                                    for weight, offset, rate in terms)
               for gap in candidates)


def verify():
    gaps = tuple(map(F, ("12.99", ".93", "2.27", ".01", "1.12")))
    h, k, q, p, c = gaps
    upper_gap = F(1, 25)
    length = h+2*k+3*q
    assert 1 < c < F(9, 5) and p < c-1
    assert p*(p+q) < F(2, 5) and p < F(13, 24) and k < F(11, 2)
    assert F(13, 24)**2*(1+F(11, 2))+F(13, 24)*F(2, 5) < 3
    assert h*q < 160*c*(2-c) and length > F(7, 5)*(2*c-1)
    gradient = c*length-MATCHING_PRICE/RATE*max(c-1-p, 0)*(4*h*q+36*c)
    assert gradient > c*length/16
    cuts, omega = endpoint_bounds(gaps, upper_gap)
    assert omega > 0 and all(difference > 0 for _, difference, _ in cuts)
    base = [score(gaps, F(0), n, v, highest_weight=F(3, 2)) for n, v in RAYS]
    assert base[RAYS.index((1, 1))] < 0
    for (n, v), constant in zip(RAYS, base, strict=True):
        slope = gradient*max(n, F(v)/2)
        assert constant+slope*upper_gap > 0
        m, D, K = cuts[0]
        highest = (64*v*m/RATE, D, K)
        for m, D, K in cuts[1:]:
            shared = (96*n*omega*m/RATE, D, K)
            assert minimum_on_interval(constant, slope, (highest, shared), upper_gap) > 1
    print("Two actual widths and all clipped quadratic minima verified exactly.")


def verify_both_gap_example():
    gaps = tuple(map(F, ("12.53", ".93", "2.58", "0", "1.17")))
    h, k, q, p, c = gaps
    upper_gap = F(1, 10)
    length = h+2*k+3*q
    assert q >= F(4, 5) and F(4, 5)*(RATE-48) > 96
    assert 1 < c < F(9, 5) and h*q < 160*c*(2-c)
    assert length > F(7, 5)*(2*c-1) and k < F(11, 2)
    gradient = c*length-MATCHING_PRICE/RATE*(c-1)*(4*h*q+36*c)
    cuts, _ = endpoint_bounds(gaps, upper_gap)
    assert all(difference > 0 for _, difference, _ in cuts)
    assert score(gaps, F(0), 1, 1, highest_weight=F(1)) < -1
    for n, v in RAYS:
        constant = score(gaps, F(0), n, v, highest_weight=F(1))
        slope = gradient*max(n, F(v)/2)
        assert constant+slope*upper_gap > 0
        m, D, K = cuts[0]
        highest = (64*v*m/RATE, D, K)
        for m, D, K in cuts[1:]:
            shared = (48*n*m/RATE, D, K)
            assert minimum_on_interval(constant, slope, (highest, shared), upper_gap) > 1


if __name__ == "__main__":
    verify()
    verify_both_gap_example()

