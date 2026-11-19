"""Exact endpoint example retaining the true highest and nominal shared cuts."""

from fractions import Fraction as F

from verify_rank7_joint_trace_prices import trace_prices, width_enclosure
from verify_rank7_monotone_fifth_gap import GEOMETRY as K, MATCHING_PRICE, RATE as A


RAYS = ((1, 0), (1, F(1, 2)), (1, F(2, 3)), (1, 1),
        (1, 2), (1, 4), (0, 1))


def best_blend(rows):
    """Maximize the smaller of the two ray margins over the blend."""
    (split_left, single_left), (split_right, single_right) = rows
    weights = [F(0), F(1)]
    difference = split_left-single_left-split_right+single_right
    if difference:
        crossing = (single_right-single_left)/difference
        if 0 < crossing < 1:
            weights.append(crossing)
    return max(min(theta*split + (1-theta)*single for split, single in rows)
               for theta in weights)


def margins():
    h, k, q, d = F(14), F(1), F(4), F(19, 20)
    x, y, length = h+k+q, k+q, h+2*k+3*q
    alpha, beta, gamma = 1+x, 1+y, 1+q
    g, delta = h*q, k*x
    tied_gain = g-h-3*q-F(5, 2)
    anti = k*k*(k*k+(h*h+q*q)/2)
    s = F(13, 20)*(g-MATCHING_PRICE*(1-d))
    t = delta
    lam, mu = 24*s/A, 24*t/A
    completion = x*y*q-lam*(y+q)-mu*q
    assert 0 < s < g and completion > 0

    shared_width, _ = width_enclosure(alpha*gamma*d, max(alpha, beta*gamma))
    inner, outer = alpha*beta*d, alpha*gamma
    weight = (inner*d-outer)/(inner*d+outer)
    assert shared_width > 0 and 0 < weight < 1
    highest_payment = (12*t*(2*delta-t)+anti+d*d*k*k/2)/(K*A)

    with_cut, without_cut = [], []
    for c in (d, F(1)):
        high_line = weight*(inner*c-outer)-weight**2*(inner*c+outer)/2
        assert high_line > 0
        shared_gain = g-MATCHING_PRICE*(c-d)
        shared_payment = (g*g+12*s*(2*shared_gain-s)
                          +d*d*g*g/(h*h+3*q*q))/(12*A)
        values, controls = [], []
        for n, v in RAYS:
            peak, mixed = max(n, v), max(n, F(v)/2)
            floor = max(F(5, 2)*n, 2*v, 2*n+v)
            increment = max(0, 2*n+v-3*mixed)
            trace_high, trace_shared = trace_prices(n, v)
            common = shared_payment*peak+highest_payment*v
            common += 96*c*shared_width*trace_shared/A
            common += (delta-mu)*((1-d)*(c-d)*max(v,F(n)/2)-d*d*v)
            split = common+k*c*d*v-(tied_gain-lam)*c*d*n
            single = common+c*d*length*mixed+d**4*floor
            single += min(d**3*q,completion)*increment-(g-lam)*c*d*n
            actual_high = 96*high_line*trace_high/A
            controls.append((split, single))
            values.append((split+actual_high, single+actual_high))
        for j in range(len(RAYS)-1):
            with_cut.append(best_blend(values[j:j+2]))
            without_cut.append(best_blend(controls[j:j+2]))
    return min(with_cut), min(without_cut)


if __name__ == "__main__":
    paid, control = margins()
    assert paid > F(1, 16)
    assert control < -F(1, 40)
    print("Both affine-cut endpoints pass with fixed shifts and margin > 1/16.")
