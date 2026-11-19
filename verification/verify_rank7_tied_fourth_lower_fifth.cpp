// Directed-integer certificate for a=b, b/d below 4/3, with freely moving c.
#define main previous_rank7_interval_main
#include "verify_rank7_equal_fifth_sixth.cpp"
#undef main

namespace fourth_tie {
using Region=std::array<Bounds,4>; // z,y,x,b, normalized to d=1
const auto one=Bounds(1), two=Bounds(2), half=Bounds::rational(1,2);
const auto width_rate=96*INV_RATE, lambda_direct=Bounds::rational(200,11);
const auto domain_limit=Bounds::rational(1800,61), two_thirds=Bounds::rational(2,3);
const std::array<Ray,7> rays={ray(1,0),ray(1,1,2),ray(1,2,3),ray(1,1),ray(1,2),ray(1,4),ray(0,1)};
const std::array<Bounds,7> shared_trace={half,half,half,two_thirds,Bounds::rational(5,6),Bounds::rational(11,12),0};
const std::array<Bounds,4> us={Bounds::rational(5,4),Bounds::rational(3,2),one,Bounds::rational(3,4)};
const std::array<Bounds,4> ws={Bounds::rational(5,4),Bounds::rational(3,2),one,Bounds::rational(7,4)};
const std::array<Bounds,3> fs={Bounds(0),half,one};

Bounds point(I64 x) {return {x,x};}
Bounds root(Bounds x) {
    return {integer_sqrt(Wide(x.lo)*SCALE),integer_sqrt(Wide(x.hi)*SCALE)+1};
}
bool compatible(I64 a,I64 b,I64 c,I64 d) {
    // Find a common convex mixture with strictly positive value at both ray endpoints.
    if(std::max(a,b)<=0 || std::max(c,d)<=0) return false;
    if((a>0 && c>0)||(b>0 && d>0)) return true;
    if(a>0) return (-Wide(c))*(Wide(a)-b)<Wide(a)*(Wide(d)-c);
    return (-Wide(a))*(Wide(c)-d)<Wide(c)*(Wide(b)-a);
}
std::optional<Region> reduce(Region box) {
    auto [z,y,x,b]=box;
    const Bounds low=point(b.lo), high=point(b.hi);
    const auto limit=domain_limit/low.square(), g_limit=160/low.square();
    x.lo=std::max({x.lo,(two_thirds/high).lo,(low-1).lo});
    z.lo=std::max(z.lo,((low-1)*(1+x+y)).lo);
    const auto z_new=(2*y+3*x)/(5*point(x.hi)-1);
    z.lo=std::max(z.lo,z_new.lo);
    if(x.lo>x.hi || z.lo>z.hi) return std::nullopt;
    z.hi=std::min(z.hi,(g_limit/point(x.lo)).hi);
    x.hi=std::min(x.hi,(g_limit/point(z.lo)).hi);
    y.hi=std::min(y.hi,(limit/(point(z.lo)+point(x.lo))).hi);
    if(y.lo>0) {
        z.hi=std::min(z.hi,(limit/point(y.lo)-point(y.lo)-point(x.lo)).hi);
        x.hi=std::min(x.hi,(limit/point(y.lo)-point(y.lo)-point(z.lo)).hi);
    }
    if(z.lo>z.hi || y.lo>y.hi || x.lo>x.hi)return std::nullopt;
    return Region{z,y,x,b};
}
enum class Result { Unknown, Old, Weighted, Shared };
Result prove(const Region& box, bool use_joint) {
    const auto [z,y,x,b]=box;
    const auto xsum=z+y+x, ysum=y+x, G=z*x, D=y*xsum, b2=b.square();
    if((z+2*y+3*x-5*G).nonnegative() || (b2*D-domain_limit).lo>0
       || (b2*G-160).lo>0 || (1-x-2*y).nonnegative()
       || (96*y-1).hi<=0 || (x-two_thirds/b).hi<=0
       || (x-(b-1)).hi<=0 || (z-(b-1)*(1+x+y)).hi<=0) return Result::Old;
    const auto z2=z.square(),x2=x.square(),y2=y.square(),g2=G.square(),d2=D.square();
    const auto R=y2*(y2+(z2+x2)/2);
    for(auto w:ws) {
        const auto payment=b2*((12*w*(2-w)*d2+R)*INV_GEOM+largest(g2/24,x2.square()/72));
        if((payment+168*y-(168-24*w)*D).lo>0) return Result::Weighted;
    }
    if(!use_joint) return Result::Unknown;

    const auto alpha=1+xsum, beta=1+ysum, gamma=1+x;
    const auto width_a=alpha*(gamma-b).positive().square()/(root(gamma)+root(b)).square();
    const auto width_b=gamma*(z-(b-1)*beta).positive().square()/(root(alpha)+root(b*beta)).square();
    const auto cut=width_rate*smallest(width_a,width_b);
    const auto H=z*(x-1)-3*x-Bounds::rational(5,2);
    const std::array<Bounds,2> ends={one,b};
    std::array<std::array<Bounds,7>,2> fixed_single{},fixed_split{};
    for(int i=0;i<2;++i) for(int j=0;j<7;++j) {
        const auto& r=rays[j];
        const auto c=ends[i], common=c*cut*shared_trace[j];
        fixed_single[i][j]=common+c*(z*(r.m-x*r.n)+(2*y+3*x)*r.m)+r.constant/b2;
        fixed_split[i][j]=common+c*(y*r.v-H*r.n);
    }
    const auto norm=z2+x2;
    unsigned done=0;
    for(auto f:fs) {
        const auto tax=(1-f)*lambda_direct;
        const auto G0=(G-tax*(1-1/b)).positive();
        const auto invQ=norm/(norm+72*f.square());
        const auto base=G0*invQ, square=G0.square()*invQ;
        for(auto u:us) {
            const auto s=u*base, lam=PRICE*s;
            const auto common_s=(g2/12+u*(2-u)*square)*b2*INV_RATE;
            for(auto w:ws) {
                const auto rho=1-PRICE*w;
                const auto T=b2*(12*w*(2-w)*d2+R)*INV_GEOM*INV_RATE;
                const auto C=(x*xsum*(x+rho*y)-lam*(y+2*x)).positive();
                std::array<std::array<std::array<I64,2>,7>,2> margins{};
                for(int i=0;i<2;++i) {
                    const auto c=ends[i], S=common_s+(i==0?2*s*tax*b*(b-1)*INV_RATE:Bounds(0));
                    const auto prefix=(b-1)*(c-1);
                    const auto geometric=smallest(x/b,c*b*C);
                    for(int j=0;j<7;++j) {
                        const auto& r=rays[j];
                        const auto common=S*r.peak+T*r.v+rho*D*(prefix*r.tail-r.v)+c*lam*r.n;
                        margins[i][j][0]=(common+fixed_split[i][j]).lo;
                        margins[i][j][1]=(common+fixed_single[i][j]+geometric*r.improvement).lo;
                    }
                }
                for(unsigned j=0;j<6;++j) {
                    if(done&(1U<<j))continue;
                    bool pass=true;
                    for(const auto& e:margins) pass=pass&&compatible(e[j][0],e[j][1],e[j+1][0],e[j+1][1]);
                    if(pass)done|=(1U<<j);
                }
                if(done==63) return Result::Shared;
            }
        }
    }
    return Result::Unknown;
}

int run(int first,int last) {
    // Slabs start from the end adjoining b=4/3; all have fixed rational endpoints.
    const std::array<Bounds,7> boundary={Bounds::rational(4,3),Bounds::rational(5,4),
        Bounds::rational(6,5),Bounds::rational(23,20),Bounds::rational(11,10),
        Bounds::rational(21,20),Bounds::rational(101,100)};
    struct Node {Region box;int depth;};
    if(first<1||last<first||last>6)throw std::invalid_argument("slabs are numbered 1 through 6");
    for(int slab=first;slab<=last;++slab) {
        Region start={Bounds(Bounds::rational(3,5).lo,190*SCALE),Bounds(Bounds::rational(1,96).lo,Bounds::rational(11,2).hi),
            Bounds(half.lo,17*SCALE),{boundary[slab].lo,boundary[slab-1].hi}};
        std::vector<Node> pending{{start,0}};
        std::array<std::uint64_t,4> counts{};
        int deep=0;
        while(!pending.empty()) {
            const auto [old,depth]=pending.back();pending.pop_back();deep=std::max(deep,depth);
            const auto reduced=reduce(old);
            auto outcome=reduced?prove(*reduced,depth>=6):Result::Old;
            if(outcome!=Result::Unknown){
                ++counts[static_cast<int>(outcome)];
                const auto sum=counts[1]+counts[2]+counts[3];
                if(sum%200000==0)std::cout<<"Slab "<<slab<<", accepted "<<sum<<", depth "<<deep<<std::endl;
                continue;
            }
            const auto box=*reduced;
            if(depth>=75){
                std::cout<<"Unresolved slab "<<slab<<":";
                for(auto v:box)std::cout<<" ["<<v.lo<<","<<v.hi<<"]/"<<SCALE;
                std::cout<<std::endl;return 2;
            }
            int dim=0;
            for(int j=1;j<4;++j){
                const auto v=box[j],w=box[dim]; const int a=j==3?3:1, d=dim==3?3:1;
                if(Wide(a)*(v.hi-v.lo)*(SCALE+w.lo)>Wide(d)*(w.hi-w.lo)*(SCALE+v.lo))dim=j;
            }
            auto l=box,r=box; const auto v=box[dim];const auto mid=v.lo+(v.hi-v.lo)/2;
            if(mid==v.lo||mid==v.hi)throw std::runtime_error("resolution exceeded");
            l[dim].hi=mid;r[dim].lo=mid;
            pending.push_back({r,depth+1});pending.push_back({l,depth+1});
        }
        std::cout<<"Complete slab "<<slab<<": old "<<counts[1]<<", weighted "<<counts[2]
                 <<", shared "<<counts[3]<<", maximum depth "<<deep<<std::endl;
    }
    return 0;
}
} // namespace fourth_tie
int main(int argc,char** argv) {
    try {const int first=argc>1?std::stoi(argv[1]):1; const int last=argc>2?std::stoi(argv[2]):6;
        return fourth_tie::run(first,last);}
    catch(const std::exception& error){std::cerr<<error.what()<<'\n';return 1;}
}
