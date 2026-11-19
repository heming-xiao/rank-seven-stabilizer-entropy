// Directed-integer corner verifier for a=b, b/d >= 4/3.
// All physical lower comparisons are bilinear in the last two probabilities.
#define main equal_fifth_sixth_reference_main
#include "verify_rank7_equal_fifth_sixth.cpp"
#undef main

namespace fourth_tie {

using TailBox = std::array<Bounds,5>; // h, k, q, c, d; a=b=1
const Bounds THIRD = Bounds::rational(1,3);
const Bounds HALF = Bounds::rational(1,2);
const Bounds TWO_THIRDS = Bounds::rational(2,3);
const std::array<Ray,7> rays={
    ray(1,0),ray(1,1,2),ray(1,2,3),ray(1,1),ray(1,2),ray(1,4),ray(0,1)
};
const std::array<Bounds,7> trace_one={
    0,Bounds::rational(3,8),Bounds::rational(4,9),TWO_THIRDS,
    Bounds::rational(4,3),Bounds::rational(8,3),TWO_THIRDS
};
const std::array<Bounds,7> trace_shared={
    HALF,HALF,HALF,TWO_THIRDS,Bounds::rational(5,6),Bounds::rational(11,12),0
};

Bounds point(I64 value) { return {value,value}; }

std::optional<TailBox> contract_tail(TailBox box) {
    const auto [h,k,q,c,d]=box;
    const Bounds cl=point(c.lo), ch=point(c.hi), dl=point(d.lo), dh=point(d.hi);
    if (c.hi<d.lo || (Bounds::rational(101,100)*dl-ch).lo>=0
        || (cl-Bounds::rational(9,5)*dh).lo>=0) return std::nullopt;
    const Bounds discount=dh-(1-dh)*cl;
    if (discount.hi<=0) return std::nullopt;
    const Bounds x_limit=Bounds::rational(1800,61)*discount;
    const Bounds g_limit=160*discount;
    const Bounds shared_floor=1/dh-1;
    const I64 ql=std::max({q.lo, shared_floor.lo, (1-2*dh*k/cl).lo,(TWO_THIRDS*dl).lo});
    const I64 hl=std::max(h.lo,(shared_floor*(1+k+q)).lo);
    const I64 kl=std::max(k.lo,((1-q)*cl/(2*dh)).lo);
    const I64 hh=std::min(h.hi,(g_limit/point(ql)).hi);
    const I64 qh=std::min(q.hi,(g_limit/point(hl)).hi);
    const I64 kh=std::min(k.hi,(x_limit/(h+q)).hi);
    if (hl>hh || kl>kh || ql>qh) return std::nullopt;
    return TailBox{Bounds(hl,hh),Bounds(kl,kh),Bounds(ql,qh),c,d};
}

Bounds support_weight(Bounds inner, Bounds outer) {
    return point(((inner-outer).positive()/(inner+outer)).lo);
}

Bounds support_value(Bounds inner, Bounds outer, Bounds w) {
    const Bounds w_half2=w.square()/2;
    return (w-w_half2)*inner-(w+w_half2)*outer;
}

// All four inputs are lower endpoints. The two linear constraints in
// the mixing parameter have a nonempty region with strict positivity.
bool blend(I64 s1,I64 t1,I64 s2,I64 t2) {
    if (std::max(s1,t1)<=0 || std::max(s2,t2)<=0) return false;
    if ((s1>0 && s2>0) || (t1>0 && t2>0)) return true;
    if (s1>0) return (-Wide(s2))*(Wide(s1)-t1)<Wide(s1)*(Wide(t2)-s2);
    return (-Wide(s1))*(Wide(s2)-t2)<Wide(s2)*(Wide(t1)-s1);
}

enum class Test { Unknown, OldRegion, Weighted, Corners };

Test compare(const TailBox& box, bool use_corners) {
    const auto [h,k,q,c,d]=box;
    const Bounds x=h+k+q,y=k+q,g=h*q,delta=k*x,L=h+2*k+3*q;
    const Bounds alpha=1+x,beta=1+y,gamma=1+q;
    const Bounds pair=alpha*gamma, upper1=alpha*beta, lower_shared=largest(alpha,beta*gamma);
    const Bounds discount=d-(1-d)*c;
    if ((L-5*g).lo>=0 || (c-c*q-2*d*k).lo>=0
        || (3-alpha).lo>=0 || (alpha+beta-alpha*beta).lo>=0
        || (Bounds::rational(7,5)*(1+c-d)-x).lo>=0
        || (c-96*d*k).lo>=0 || (lower_shared-pair*d).lo>=0
        || (c*d-x*discount).lo>=0 || (delta-Bounds::rational(1800,61)*discount).lo>0
        || (g-160*discount).lo>0) return Test::OldRegion;

    const Bounds h2=h.square(),q2=q.square(),k2=k.square(),g2=g.square(),d2=delta.square();
    const Bounds anti=k2*(k2+(h2+q2)/2);
    const Bounds cut_one=gap_square(upper1*c*d,pair);
    for (const Bounds u:{Bounds(1),Bounds::rational(5,4),Bounds::rational(3,2)}) {
        const Bounds payment=(12*u*(2-u)*d2+anti)*INV_GEOM
            +largest(g2/24,q2.square()/72)+64*cut_one;
        const Bounds debit=(168-24*u)*delta*discount-168*k*c*d;
        if ((payment-debit).lo>0) return Test::Weighted;
    }
    // All relevant points are ordered; independently subdivide boxes
    // which still contain an unordered corner.
    if (!use_corners || c.lo<d.hi) return Test::Unknown;

    const Bounds cl=point(c.lo),ch=point(c.hi),dl=point(d.lo),dh=point(d.hi);
    const std::array<Bounds,4> cv={cl,ch,cl,ch},dv={dl,dl,dh,dh};
    const Bounds ws=support_weight(pair*dl,lower_shared);
    const Bounds w1=support_weight(upper1*cl*dl,pair);
    const Bounds psi_tail=largest(Bounds::rational(1,13),
        (cl-dh).positive().square()+((1-ch).square()+dl.square())/6);
    const Bounds psi=(h2+q2)/6+psi_tail, odd_denom=h2+3*q2;
    const Bounds cubic=x*y*q,H=g-h-3*q-Bounds::rational(5,2);
    struct Corner { Bounds c,d,cd,dsq,d4,prefix,odd,spread; };
    std::array<Corner,4> corner{};
    std::array<std::array<Bounds,7>,4> cuts{};
    for (int tail=0;tail<4;++tail) {
        const Bounds c0=cv[tail],d0=dv[tail],dsq=d0.square(),cd=c0*d0;
        const Bounds odd=(1-ch)*(1+ch-2*c0)+dl*(2*d0-dl);
        corner[tail]={c0,d0,cd,dsq,dsq.square(),(1-d0)*(c0-d0),odd,c0-d0};
        const Bounds one=support_value(upper1*cd,pair,w1);
        const Bounds shared=c0*support_value(pair*d0,lower_shared,ws);
        for (int j=0;j<7;++j) cuts[tail][j]=96*INV_RATE*(one*trace_one[j]+shared*trace_shared[j]);
    }
    unsigned done=0;
    for (const Bounds f:{Bounds(0),HALF,Bounds(1),Bounds::rational(1,4),Bounds::rational(3,4)}) {
        const Bounds price=(1-f)*Bounds::rational(200,11);
        const Bounds g0=(g-price*(ch-dl)).positive();
        const Bounds qinv=psi/(psi+12*f.square());
        for (const Bounds u:{Bounds::rational(5,4),Bounds(1),Bounds::rational(3,4),Bounds::rational(3,2)}) {
            if (g0.hi==0 && u.hi!=SCALE) continue;
            const Bounds s=u*g0*qinv, lambda=PRICE*s;
            const Bounds shared_quad=12*u*(2-u)*g0.square()*qinv;
            for (const Bounds w:HIGHEST_SHIFTS) {
                const Bounds mu=PRICE*w*delta, highest_residual=delta-mu;
                const Bounds C=(cubic-lambda*(y+q)-mu*q).positive();
                const Bounds highest_quad=12*w*(2-w)*d2+anti;
                std::array<std::array<std::array<I64,2>,7>,4> m{};
                for (int tail=0;tail<4;++tail) {
                    const Corner& z=corner[tail];
                    const Bounds physical_shared=(g2+shared_quad+24*s*price*(ch-dl-z.spread)
                        +z.odd*g2/odd_denom)*INV_RATE/12;
                    const Bounds physical_high=(highest_quad+z.odd*k2/2)*INV_RATE*INV_GEOM;
                    const Bounds increment=smallest(z.dsq*z.d*q,z.c*C);
                    const Bounds singleton=z.cd*L;
                    const Bounds split_debit=z.cd*(H-lambda), single_debit=z.cd*(g-lambda);
                    for (int j=0;j<7;++j) {
                        const Ray& r=rays[j];
                        const Bounds base=physical_shared*r.peak+physical_high*r.v+cuts[tail][j]
                            +highest_residual*(z.prefix*r.tail-z.dsq*r.v);
                        m[tail][j][0]=(base+z.cd*k*r.v-split_debit*r.n).lo;
                        m[tail][j][1]=(base+singleton*r.m+z.d4*r.constant+
                            increment*r.improvement-single_debit*r.n).lo;
                    }
                }
                for (unsigned j=0;j<6;++j) {
                    if (done&(1u<<j)) continue;
                    bool works=true;
                    for (const auto& mm:m) {
                        works=works&&blend(mm[j][0],mm[j][1],mm[j+1][0],mm[j+1][1]);
                    }
                    if (works) done|=1u<<j;
                }
                if (done==63) return Test::Corners;
            }
        }
    }
    return Test::Unknown;
}

int cover(const std::vector<Bounds>& d_boundaries) {
    struct Node { TailBox box; int depth; };
    std::array<std::uint64_t,4> totals{};
    int max_depth=0;
    for (std::size_t slab=0;slab+1<d_boundaries.size();++slab) {
        const auto prior=totals;
        const I64 dlo=d_boundaries[slab].lo,dhi=d_boundaries[slab+1].hi;
        const Bounds floor=point(dlo);
        const TailBox initial{Bounds(Bounds::rational(3,5).lo,143*SCALE),
            Bounds(0,Bounds::rational(33,8).hi),Bounds(HALF.lo,Bounds::rational(51,4).hi),
            Bounds(floor.lo,(Bounds::rational(9,5)*point(dhi)).hi< SCALE
                           ? (Bounds::rational(9,5)*point(dhi)).hi:SCALE),
            Bounds(dlo,dhi)};
        std::vector<Node> pending{{initial,0}};
        while (!pending.empty()) {
            const Node node=pending.back();
            pending.pop_back();
            max_depth=std::max(max_depth,node.depth);
            const auto contracted=contract_tail(node.box);
            const Test result=contracted ? compare(*contracted,node.depth>=9) : Test::OldRegion;
            if (result!=Test::Unknown) {
                ++totals[static_cast<int>(result)];
                const std::uint64_t leaves=totals[1]+totals[2]+totals[3];
                if (leaves%100000==0) {
                    std::cout<<leaves<<" accepted, slab "<<slab+1<<", depth "<<max_depth<<'\n'<<std::flush;
                }
                continue;
            }
            if (node.depth>=72) {
                std::cerr<<"Unresolved a=b slab "<<slab+1<<":";
                for (const Bounds z:*contracted) std::cerr<<" ["<<z.lo<<","<<z.hi<<"]/"<<SCALE;
                std::cerr<<'\n';
                return 2;
            }
            std::size_t axis=0;
            const std::array<I64,5> weights={1,1,1,4,6};
            for (std::size_t j=1;j<weights.size();++j) {
                const Bounds a=(*contracted)[j], b=(*contracted)[axis];
                if (Wide(weights[j])*(a.hi-a.lo)*(SCALE+b.lo)
                    > Wide(weights[axis])*(b.hi-b.lo)*(SCALE+a.lo)) axis=j;
            }
            const Bounds z=(*contracted)[axis];
            const I64 mid=z.lo+(z.hi-z.lo)/2;
            if (mid==z.lo || mid==z.hi) throw std::runtime_error("dyadic split reached resolution");
            TailBox left=*contracted,right=*contracted;
            left[axis].hi=mid;
            right[axis].lo=mid;
            pending.push_back({right,node.depth+1});
            pending.push_back({left,node.depth+1});
        }
        std::cout<<"Completed slab "<<slab+1<<" with "
                 <<totals[1]+totals[2]+totals[3]-prior[1]-prior[2]-prior[3]
                 <<" leaves at observed depth "<<max_depth<<'\n'<<std::flush;
    }
    std::cout<<"Verified "<<totals[1]+totals[2]+totals[3]<<" exact leaves at depth "<<max_depth
             <<": old domain "<<totals[1]<<", weighted "<<totals[2]<<", bilinear "<<totals[3]<<'\n';
    return 0;
}

} // namespace fourth_tie

int main(int argc, char** argv) {
    try {
        if (argc == 1) {
            return fourth_tie::cover({
                fourth_tie::HALF, Bounds::rational(9,16), Bounds::rational(5,8),
                Bounds::rational(2,3), Bounds::rational(7,10), Bounds::rational(3,4)
            });
        }
        if (argc != 4) {
            throw std::invalid_argument("Usage: verifier [lower-numerator upper-numerator denominator]");
        }
        const auto parse = [](const std::string& arg) {
            std::size_t end = 0;
            const I64 value = std::stoll(arg, &end);
            if (end != arg.size() || value <= 0 || value > SCALE) {
                throw std::invalid_argument("Expected a positive integer no larger than the fixed-point scale");
            }
            return value;
        };
        const I64 lower = parse(argv[1]);
        const I64 upper = parse(argv[2]);
        const I64 denominator = parse(argv[3]);
        if (2*lower < denominator || lower >= upper || 4*upper > 3*denominator) {
            throw std::invalid_argument("Expected an increasing subinterval of [1/2, 3/4]");
        }
        std::cout << "Requested d/b interval [" << lower << "/" << denominator
                  << "," << upper << "/" << denominator << "]\n" << std::flush;
        return fourth_tie::cover({Bounds::rational(lower,denominator), Bounds::rational(upper,denominator)});
    }
    catch (const std::exception& error) { std::cerr<<error.what()<<'\n'; return 1; }
}

