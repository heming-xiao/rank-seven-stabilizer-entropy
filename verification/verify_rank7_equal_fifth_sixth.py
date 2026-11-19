"""Interval checker for rank seven with equal fifth and sixth probabilities."""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache
from math import isqrt

from verify_rank7_four_equal_tails import EXTERIOR_RATE
from verify_rank7_three_equal_tails import RAYS


SCALE = 1 << 44
GEOMETRY = F(5, 2)


@dataclass(frozen=True, slots=True)
class Bounds:
    lo: int
    hi: int

    @staticmethod
    @cache
    def point(value):
        fraction = F(value) * SCALE
        return Bounds(fraction.numerator // fraction.denominator,
                      -(-fraction.numerator // fraction.denominator))

    def __add__(self, other):
        if not isinstance(other, Bounds):
            other = Bounds.point(other)
        return Bounds(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Bounds(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -other

    def __rsub__(self, other):
        return other + -self

    def __mul__(self, other):
        if not isinstance(other, Bounds):
            other = Bounds.point(other)
        products = (self.lo*other.lo, self.lo*other.hi, self.hi*other.lo, self.hi*other.hi)
        return Bounds(min(products) // SCALE, -(-max(products) // SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        if not isinstance(other, Bounds):
            return self * (1 / F(other))
        if other.lo <= 0:
            raise ZeroDivisionError("Denominator is not certified positive")
        lower = min((value*SCALE)//den for value in (self.lo, self.hi) for den in (other.lo, other.hi))
        upper = max(-((-value*SCALE)//den) for value in (self.lo, self.hi) for den in (other.lo, other.hi))
        return Bounds(lower, upper)

    def square(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo*self.lo, self.hi*self.hi)
        high = max(self.lo*self.lo, self.hi*self.hi)
        return Bounds(low // SCALE, -(-high // SCALE))

    def positive(self):
        return Bounds(max(0, self.lo), max(0, self.hi))


def smallest(left, right):
    return Bounds(min(left.lo, right.lo), min(left.hi, right.hi))


def largest(left, right):
    return Bounds(max(left.lo, right.lo), max(left.hi, right.hi))


def gap_lower_square(
    first: Bounds, second: Bounds, factor: Bounds,
):
    """Bound the square of the positive difference of two square roots."""
    return factor * (first-second).positive().square() / (2*(first+second))


def unresolved_subbox(box):
    h, k, q, p, c = box
    # The strict inequalities on an unresolved spectrum come from failure of
    # the small-shared, pure-exterior, and weighted-residual comparisons.
    discount_hi = (1-p.square()-(c-1).square()).hi
    if discount_hi <= 0:
        return None
    discount_limit = Bounds(discount_hi, discount_hi)
    delta_limit = F(1800, 61)*discount_limit
    g_limit = 160*discount_limit
    c_min = Bounds(c.lo, c.lo)
    k_hi = min(k.hi, (delta_limit/(h+q)).hi)
    q_hi = q.hi
    h_hi = min(h.hi, (g_limit/q).hi)
    if h.lo > 0:
        q_hi = min(q_hi, (g_limit/h).hi)
    q_hi = min(q_hi, 17*(isqrt(discount_hi*SCALE)+1))
    if k.lo > 0:
        x_limit = delta_limit/Bounds(k.lo, k.lo)
        h_hi = min(h_hi, x_limit.hi-k.lo-q.lo)
        q_hi = min(q_hi, x_limit.hi-k.lo-h.lo)
    h_lo = max(h.lo, (F(3, 5)*c_min).lo)
    q_lo = max(q.lo, (c_min/5).lo, (c_min-2*k/c_min).lo)
    k_lo = max(k.lo, ((c_min-q)*c_min/2).lo)
    if h_lo > h_hi or k_lo > k_hi or q_lo > q_hi:
        return None
    return (Bounds(h_lo,h_hi), Bounds(k_lo,k_hi), Bounds(q_lo,q_hi), p, c)


def sufficient(box, try_joint=True):

    h, k, q, p, c = box
    e = c-1
    a = c+p
    length = h+2*k+3*q
    g = h*q
    x = h+k+q
    y = k+q
    gamma = a+q
    beta = a+y
    alpha = a+x
    c2 = c.square()
    if (c*length-5*g).lo >= 0:
        return "small shared"
    if (c2-c*q-2*k).lo >= 0 or (p*(p+q)-c).lo >= 0:
        return "pure exterior"
    tail = p.square()+e.square()
    completion = p*q
    discount = 1-tail
    transport = c2+completion*(h/2+k+2*q+3*p+c-1)-x*discount
    if transport.lo >= 0 or (tail+completion/2-1).lo >= 0:
        return "tail transport"
    if ((3*c-alpha).lo >= 0 or (a*(alpha+beta)-alpha*beta).lo >= 0
            or (F(7,5)*(2*c-1)-x).lo >= 0):
        return "earlier analytic"

    delta = k*x
    r = k.square()*(k.square()+(h.square()+q.square())/2)
    cut_one = gap_lower_square(beta*c, gamma*a*c, alpha)
    anti_shared = largest(g.square()/24, q.square().square()/72)
    shift_gain = smallest(delta, GEOMETRY*absolute(discount-completion)).square()*(12/GEOMETRY)
    highest = ((12*delta.square()+r)/GEOMETRY + anti_shared + 64*cut_one
               - (144*delta*discount - 168*k*c2)
               + 168*completion*k*(F(6,7)*x+q+3*p+c-1-h/2) + shift_gain)
    if highest.lo >= 0:
        return "weighted residual"

    if not try_joint:
        return None

    cube = x*y*q
    f = a*cube
    denominator = c*g+2*f
    cut_two = Bounds.point(0)
    if denominator.lo > 0:
        score_in = alpha*gamma*c
        score_out = largest(alpha*a*c2, beta*gamma*a*c)
        cut_two = (f-delta/3).positive()/denominator * gap_lower_square(
            score_in, score_out, Bounds.point(1),
        )

    # The shared rank-six and odd-rank head reserves use disjoint slots.
    if (h.square()+3*q.square()).lo > 0:
        extra_shared = g.square()/(h.square()+3*q.square())
    else:
        extra_shared = Bounds.point(0)
    rho = smallest(c*e, (p+q)*p)
    tail_loss = (c*e-rho).positive()
    psi = e.square()+(h.square()+q.square()+1)/6
    aux = 1 + 12*(tail_loss/e).square()/psi
    old_gain = (g-F(200,11)*tail_loss).positive()
    quad_one = r+k.square()/2
    quad_share = g.square()+extra_shared
    common = (length*p.square()*(a-1)+p.square().square()+3*y*q*p.square())
    price = 24/EXTERIOR_RATE

    for gain, correction in ((g, aux), (old_gain, Bounds.point(1))):
        for s_scale in (F(5,4), 1, F(3,2), F(3,4)):
            shared_shift = gain*s_scale/correction
            lam = price*shared_shift
            paid_share = quad_share+12*s_scale*(2-s_scale)*gain.square()/correction
            for t_scale in (F(5,4), F(3,2), F(7,4), 1):
                mu = price*t_scale*delta
                paid_one = quad_one+12*t_scale*(2-t_scale)*delta.square()
                completion_price = (cube-lam*(y+q)-mu*q).positive()
                head = common+2*(g-lam)*p.square()+(delta-mu)*p.square()+completion_price*p
                geom = smallest(q, c*completion_price)
                paid_n = (g-lam)*c
                paid_v = delta-mu
                for n, v in RAYS:
                    max_pair = max(n, v)
                    singleton = max(n, F(v)/2)
                    constant = max(F(5,2)*n, 2*v, 2*n+v)
                    improvement = max(0, 2*n+v-3*singleton)
                    lhs = (c2*length*singleton+constant+head*max_pair
                           +paid_v*e.square()*max(v, F(n)/2)+geom*improvement
                           +paid_share*max_pair/(12*EXTERIOR_RATE)
                           +paid_one*v/(GEOMETRY*EXTERIOR_RATE)
                           +(64*v*cut_one+96*n*cut_two)/EXTERIOR_RATE
                           -paid_n*n-paid_v*v)
                    if lhs.lo < 0:
                        break
                else:
                    return "joint prices"
    return None


def absolute(value):
    lower = 0 if value.lo <= 0 <= value.hi else min(abs(value.lo), abs(value.hi))
    return Bounds(lower, max(abs(value.lo), abs(value.hi)))


def initial_box():
    limits = ((0,190), (0,F(11,2)), (F(1,5),17), (0,1), (F(101,100),2))
    return tuple(Bounds(Bounds.point(lo).lo, Bounds.point(hi).hi) for lo, hi in limits)


def main():
    root = initial_box()
    widths = tuple(value.hi-value.lo for value in root)
    pending = [(root, 0)]
    counts = Counter()
    deepest = 0
    next_progress = 5000
    while pending:
        box, depth = pending.pop()
        deepest = max(depth, deepest)
        box = unresolved_subbox(box)
        if box is None:
            counts["strict outer bounds"] += 1
            continue
        reason = sufficient(box, try_joint=depth >= 10)
        if reason is not None:
            counts[reason] += 1
            continue
        if depth == 75:
            coords = [(float(F(x.lo,SCALE)), float(F(x.hi,SCALE))) for x in box]
            raise ArithmeticError(f"Unverified box at depth {depth}: {coords}")
        axis = max(range(5), key=lambda i: F(box[i].hi-box[i].lo, widths[i]))
        end = box[axis]
        mid = (end.lo+end.hi)//2
        left = box[:axis]+(Bounds(end.lo, mid),)+box[axis+1:]
        right = box[:axis]+(Bounds(mid, end.hi),)+box[axis+1:]
        pending.append((right, depth+1))
        pending.append((left, depth+1))
        total = counts.total()
        if total >= next_progress:
            print(f"At {total} accepted leaves, depth {deepest}; {dict(counts)}.", flush=True)
            next_progress += 5000
    print(f"Equal fifth and sixth: {dict(counts)}, maximum depth {deepest}.", flush=True)


if __name__ == "__main__":
    main()

