// Exact directed-integer interval checker for equal fifth and sixth weights.
// Implements the comparison in literature/rank7_equal_fifth_sixth_candidate.md.

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string_view>
#include <vector>

using I64 = std::int64_t;
using Wide = __int128_t;
constexpr I64 SCALE = I64{1} << 27;

I64 narrow(Wide value) {
    if (value < std::numeric_limits<I64>::min() || value > std::numeric_limits<I64>::max()) {
        throw std::overflow_error("interval endpoint exceeds the integer range");
    }
    return static_cast<I64>(value);
}

Wide floor_ratio(Wide numerator, I64 denominator) {
    const Wide quotient = numerator / denominator;
    return quotient - (numerator % denominator < 0 ? 1 : 0);
}

Wide ceil_ratio(Wide numerator, I64 denominator) {
    return -floor_ratio(-numerator, denominator);
}

struct Bounds {
    I64 lo;
    I64 hi;

    Bounds(I64 lower, I64 upper) : lo(lower), hi(upper) {}
    Bounds(I64 value = 0) : lo(narrow(Wide(value) * SCALE)), hi(lo) {}

    static Bounds rational(I64 numerator, I64 denominator) {
        const Wide raw = Wide(numerator) * SCALE;
        return {narrow(floor_ratio(raw, denominator)), narrow(ceil_ratio(raw, denominator))};
    }

    bool nonnegative() const { return lo >= 0; }

    Bounds positive() const { return {std::max<I64>(0, lo), std::max<I64>(0, hi)}; }

    Bounds absolute() const {
        const Wide lo_abs = lo < 0 ? -Wide(lo) : Wide(lo);
        const Wide hi_abs = hi < 0 ? -Wide(hi) : Wide(hi);
        const Wide small = lo <= 0 && hi >= 0 ? 0 : std::min(lo_abs, hi_abs);
        return {narrow(small), narrow(std::max(lo_abs, hi_abs))};
    }

    Bounds square() const {
        const Bounds magnitude = absolute();
        return {narrow(floor_ratio(Wide(magnitude.lo) * magnitude.lo, SCALE)),
                narrow(ceil_ratio(Wide(magnitude.hi) * magnitude.hi, SCALE))};
    }
};

Bounds operator+(Bounds a, Bounds b) {
    return {narrow(Wide(a.lo) + b.lo), narrow(Wide(a.hi) + b.hi)};
}
Bounds operator-(Bounds a, Bounds b) {
    return {narrow(Wide(a.lo) - b.hi), narrow(Wide(a.hi) - b.lo)};
}
Bounds operator*(Bounds a, Bounds b) {
    const Wide p = Wide(a.lo) * b.lo;
    const Wide q = Wide(a.lo) * b.hi;
    const Wide r = Wide(a.hi) * b.lo;
    const Wide s = Wide(a.hi) * b.hi;
    return {narrow(floor_ratio(std::min({p,q,r,s}), SCALE)),
            narrow(ceil_ratio(std::max({p,q,r,s}), SCALE))};
}
Bounds operator/(Bounds a, Bounds b) {
    if (b.lo <= 0) {
        throw std::domain_error("interval denominator is not positive");
    }
    const I64 den_for_lower = a.lo < 0 ? b.lo : b.hi;
    const I64 den_for_upper = a.hi < 0 ? b.hi : b.lo;
    return {narrow(floor_ratio(Wide(a.lo) * SCALE, den_for_lower)),
            narrow(ceil_ratio(Wide(a.hi) * SCALE, den_for_upper))};
}
Bounds smallest(Bounds a, Bounds b) { return {std::min(a.lo,b.lo),std::min(a.hi,b.hi)}; }
Bounds largest(Bounds a, Bounds b) { return {std::max(a.lo,b.lo),std::max(a.hi,b.hi)}; }

I64 integer_sqrt(Wide value) {
    I64 root = narrow(static_cast<Wide>(std::sqrt(static_cast<long double>(value))));
    while (Wide(root) * root > value) { --root; }
    while ((Wide(root) + 1) * (Wide(root) + 1) <= value) { ++root; }
    return root;
}

using Box = std::array<Bounds,5>;

std::optional<Box> contract(Box box) {
    const auto [h,k,q,p,c] = box;
    const I64 discount_hi = (1 - p.square() - (c-1).square()).hi;
    if (discount_hi <= 0) { return std::nullopt; }
    const Bounds discount_limit(discount_hi, discount_hi);
    const Bounds delta_limit = Bounds::rational(1800,61)*discount_limit;
    const Bounds g_limit = 160*discount_limit;
    const Bounds c_min(c.lo,c.lo);

    const I64 k_hi = std::min(k.hi, (delta_limit/(h+q)).hi);
    I64 q_hi = std::min(q.hi, narrow(17*(Wide(integer_sqrt(Wide(discount_hi)*SCALE))+1)));
    I64 h_hi = std::min(h.hi, (g_limit/q).hi);
    if (h.lo > 0) { q_hi = std::min(q_hi, (g_limit/h).hi); }
    if (k.lo > 0) {
        const Bounds x_limit = delta_limit/Bounds(k.lo,k.lo);
        h_hi = std::min(h_hi, narrow(Wide(x_limit.hi)-k.lo-q.lo));
        q_hi = std::min(q_hi, narrow(Wide(x_limit.hi)-k.lo-h.lo));
    }
    const I64 h_lo = std::max(h.lo, (Bounds::rational(3,5)*c_min).lo);
    const I64 q_lo = std::max({q.lo, (c_min/5).lo, (c_min-2*k/c_min).lo});
    const I64 k_lo = std::max(k.lo, ((c_min-q)*c_min/2).lo);
    if (h_lo > h_hi || k_lo > k_hi || q_lo > q_hi) { return std::nullopt; }
    return Box{Bounds(h_lo,h_hi), Bounds(k_lo,k_hi), Bounds(q_lo,q_hi), p, c};
}

Bounds gap_square(Bounds first, Bounds second, Bounds factor = 1) {
    return factor*(first-second).positive().square()/(2*(first+second));
}

enum class Reason {
    Unknown, SmallShared, PureExterior, TailTransport, EarlierAnalytic, WeightedResidual, Joint, Outer, Count
};
constexpr std::array<std::string_view,8> REASONS = {
    "unknown", "small shared", "pure exterior", "tail transport", "earlier analytic",
    "weighted residual", "joint prices", "strict outer bounds"
};

struct Ray {
    Bounds n, v, m, peak, constant, improvement, tail;
};

Ray ray(I64 n, I64 v_num, I64 v_den = 1) {
    const Bounds nb(n), vb = Bounds::rational(v_num,v_den);
    const Bounds m = largest(nb,vb/2);
    return {nb, vb, m, largest(nb,vb),
            largest(largest(Bounds::rational(5,2)*nb,2*vb),2*nb+vb),
            (2*nb+vb-3*m).positive(),largest(vb,nb/2)};
}

const std::array<Ray,6> RAYS = {
    ray(1,0),ray(1,1,2),ray(1,1),ray(1,2),ray(1,4),ray(0,1)
};
const Bounds RATE = Bounds::rational(4242,25);
const Bounds INV_RATE = 1/RATE;
const Bounds GEOM = Bounds::rational(5,2);
const Bounds INV_GEOM = 1/GEOM;
const Bounds PRICE = 24*INV_RATE;
const std::array<Bounds,4> SHARED_SHIFTS = {
    Bounds::rational(5,4), Bounds(1), Bounds::rational(3,2), Bounds::rational(3,4)
};
const std::array<Bounds,4> HIGHEST_SHIFTS = {
    Bounds::rational(5,4), Bounds::rational(3,2), Bounds::rational(7,4), Bounds(1)
};

Reason sufficient(const Box& box, bool try_joint) {
    const auto [h,k,q,p,c] = box;
    const Bounds e = c-1, a = c+p, length = h+2*k+3*q, g = h*q;
    const Bounds x = h+k+q, y = k+q, gamma = a+q, beta = a+y, alpha = a+x;
    const Bounds c2 = c.square(), p2 = p.square(), e2 = e.square();
    if ((c*length-5*g).nonnegative()) { return Reason::SmallShared; }
    if ((c2-c*q-2*k).nonnegative() || (p*(p+q)-c).nonnegative()) {
        return Reason::PureExterior;
    }
    const Bounds tail = p2+e2, completion = p*q, discount = 1-tail;
    const Bounds transport = c2+completion*(h/2+k+2*q+3*p+c-1)-x*discount;
    if (transport.nonnegative() || (tail+completion/2-1).nonnegative()) {
        return Reason::TailTransport;
    }
    if ((3*c-alpha).nonnegative() || (a*(alpha+beta)-alpha*beta).nonnegative()
        || (Bounds::rational(7,5)*(2*c-1)-x).nonnegative()) {
        return Reason::EarlierAnalytic;
    }

    const Bounds delta = k*x, delta2 = delta.square(), k2 = k.square();
    const Bounds h2 = h.square(), q2 = q.square(), g2 = g.square();
    const Bounds anti = k2*(k2+(h2+q2)/2);
    const Bounds cut_one = gap_square(beta*c,gamma*a*c,alpha);
    const Bounds reserve = largest(g2/24,q2.square()/72);
    const Bounds shift_gain = smallest(delta,GEOM*(discount-completion).absolute()).square()*12*INV_GEOM;
    const Bounds highest = (12*delta2+anti)*INV_GEOM+reserve+64*cut_one
        -(144*delta*discount-168*k*c2)
        +168*completion*k*(Bounds::rational(6,7)*x+q+3*p+c-1-h/2)+shift_gain;
    if (highest.nonnegative()) { return Reason::WeightedResidual; }
    if (!try_joint) { return Reason::Unknown; }

    const Bounds cubic = x*y*q, f = a*cubic, denominator = c*g+2*f;
    Bounds cut_two = 0;
    if (denominator.lo > 0) {
        cut_two = (f-delta/3).positive()/denominator
            *gap_square(alpha*gamma*c,largest(alpha*a*c2,beta*gamma*a*c));
    }
    Bounds extra_shared = 0;
    const Bounds extra_denominator = h2+3*q2;
    if (extra_denominator.lo > 0) { extra_shared = g2/extra_denominator; }
    const Bounds tail_loss = (c*e-smallest(c*e,(p+q)*p)).positive();
    const Bounds psi = e2+(h2+q2+1)/6;
    const Bounds aux = 1+12*(tail_loss/e).square()/psi;
    const Bounds old_gain = (g-Bounds::rational(200,11)*tail_loss).positive();
    const Bounds quad_one = anti+k2/2, quad_share = g2+extra_shared;
    const Bounds common = length*p2*(a-1)+p2.square()+3*y*q*p2;
    const Bounds singleton_price = c2*length;

    std::array<Bounds,6> fixed;
    for (std::size_t j=0; j<RAYS.size(); ++j) {
        const auto& r = RAYS[j];
        fixed[j] = singleton_price*r.m+r.constant+(64*r.v*cut_one+96*r.n*cut_two)*INV_RATE;
    }
    for (const auto& [gain,correction] : {std::pair{g,aux},std::pair{old_gain,Bounds(1)}}) {
        const Bounds ratio = gain/correction;
        const Bounds ratio2 = gain.square()/correction;
        for (const Bounds s : SHARED_SHIFTS) {
            const Bounds lam = PRICE*ratio*s;
            const Bounds shared_payment = (quad_share+12*s*(2-s)*ratio2)*INV_RATE/12;
            const Bounds shared_residual = g-lam;
            const Bounds paid_n = shared_residual*c;
            for (const Bounds t : HIGHEST_SHIFTS) {
                const Bounds mu = PRICE*t*delta;
                const Bounds paid_v = delta-mu;
                const Bounds highest_payment = (quad_one+12*t*(2-t)*delta2)*INV_RATE*INV_GEOM;
                const Bounds cc = (cubic-lam*(y+q)-mu*q).positive();
                const Bounds head = common+(2*shared_residual+paid_v)*p2+cc*p;
                const Bounds geom = smallest(q,c*cc);
                const Bounds tail_payment = paid_v*e2;
                bool passed = true;
                for (std::size_t j=0; j<RAYS.size(); ++j) {
                    const auto& r = RAYS[j];
                    const Bounds margin = fixed[j]+(head+shared_payment)*r.peak
                        +tail_payment*r.tail+geom*r.improvement+highest_payment*r.v
                        -paid_n*r.n-paid_v*r.v;
                    if (!margin.nonnegative()) { passed = false; break; }
                }
                if (passed) { return Reason::Joint; }
            }
        }
    }
    return Reason::Unknown;
}

Box initial_box() {
    return {Bounds(0,190*SCALE), Bounds(0,Bounds::rational(11,2).hi),
            Bounds(Bounds::rational(1,5).lo,17*SCALE), Bounds(0,SCALE),
            Bounds(Bounds::rational(101,100).lo,2*SCALE)};
}

struct Node { Box box; int depth; };

int main(int argc, char** argv) {
    try {
        const auto limit = argc == 2 ? std::stoull(argv[1]) : 0ULL;
        const Box root = initial_box();
        std::array<I64,5> widths{};
        for (std::size_t i=0; i<widths.size(); ++i) { widths[i] = root[i].hi-root[i].lo; }
        std::vector<Node> pending{{root,0}};
        std::array<std::uint64_t,static_cast<int>(Reason::Count)> counts{};
        int deepest = 0;
        std::uint64_t leaves = 0;
        while (!pending.empty()) {
            const Node node = pending.back();
            pending.pop_back();
            deepest = std::max(deepest,node.depth);
            const auto clipped = contract(node.box);
            const Reason reason = clipped ? sufficient(*clipped,node.depth>=10) : Reason::Outer;
            if (reason != Reason::Unknown) {
                ++counts[static_cast<int>(reason)];
                ++leaves;
                if (leaves % 100000 == 0 || (limit && leaves>=limit)) {
                    std::cout << leaves << " accepted, depth " << deepest << ", pending " << pending.size()
                        << ", top-gap front " << double(node.box[0].lo)/SCALE << '\n' << std::flush;
                }
                if (limit && leaves>=limit) { return 2; }
                continue;
            }

            if (node.depth == 75) {
                for (const Bounds b : *clipped) {
                    std::cerr << "[" << b.lo << "," << b.hi << "]/" << SCALE << ' ';
                }
                std::cerr << '\n';
                throw std::runtime_error("unverified box at maximum depth");
            }
            std::size_t axis = 0;
            for (std::size_t j=1; j<widths.size(); ++j) {
                const auto& next = (*clipped)[j];
                const auto& current = (*clipped)[axis];
                if (Wide(next.hi-next.lo)*widths[axis] > Wide(current.hi-current.lo)*widths[j]) { axis=j; }
            }
            const Bounds end = (*clipped)[axis];
            const I64 midpoint = end.lo+(end.hi-end.lo)/2;
            if (midpoint==end.lo || midpoint==end.hi) {
                throw std::runtime_error("interval reached the dyadic precision limit");
            }
            Box left=*clipped, right=*clipped;
            left[axis].hi=right[axis].lo=midpoint;
            pending.push_back({right,node.depth+1});
            pending.push_back({left,node.depth+1});
        }
        std::cout << "Equal fifth and sixth verified: " << leaves << " leaves, depth " << deepest << '\n';
        for (std::size_t i=1; i<counts.size(); ++i) {
            std::cout << REASONS[i] << ": " << counts[i] << '\n';
        }
        return 0;
    } catch (const std::exception& e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}

