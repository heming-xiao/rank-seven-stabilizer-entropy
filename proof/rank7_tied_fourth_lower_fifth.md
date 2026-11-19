# A directed-integer certificate for a fourth–fifth tie below the 4/3 ratio

Write the seven ordered probabilities as
\((\alpha,\beta,\gamma,b,b,c,1)\). The target includes every
\(1\le c\le b\); the sixth value moves independently of the equal
fourth and fifth values. This certificate uses the paid nominal
shared interval, without highest-pair compression. It covers a slab
only when its finite traversal has finished.

The input comparison and allocation of its crossing to the two
alternative exterior estimates are proved in the
[sixth-probability endpoint note](rank7_positive_shared_tail_endpoints.md).
Here \(z=(\alpha-\beta)/b,\ y=(\beta-\gamma)/b,\ x=(\gamma-b)/b\),
\(G=zx,\ D=y(z+y+x),\ R'=y^2[y^2+(z^2+x^2)/2]\).
Put \(A=1.01\cdot168,\ K=5/2\), and
\(H'=z(x-1)-3x-5/2\). The established global reductions leave
\(101/100\le b\le4/3,\ x\ge1/2,\ bx\ge2/3\) here. The branch with
zero nominal shared width is independently solved. Its complement
has \(x>b-1,\ z>(b-1)(1+x+y)\).

## Common physical shifts and affine endpoint margins

Let \(f\in\{0,1/2,1\}\), \(u\in\{5/4,3/2,1,3/4\}\),
\(w\in\{5/4,3/2,1,7/4\}\). Set
\[
 \begin{gathered}
 \Lambda=(1-f)200/11,\quad Q=1+72 f^2/(z^2+x^2),\\
 G_0=(G-\Lambda(1-1/b))_+,\quad s'=uG_0/Q,\quad
 \lambda'=24s'/A,\qquad \rho=1-24w/A .
 \end{gathered}
\]
The physical shifts are \(s=b^2s'\) and \(t=b^2 wD\). They are
common to both tail endpoints. In units of \(Ab^2\), the leading
mixed and anticommuting payments beyond their linear probe terms are
\[
 \begin{aligned}
 S_c&={b^2\over A}\left[G^2/12+u(2-u)G_0^2/Q+
                       2s'\Lambda(1-c/b)\right],\\
 T&={b^2\over KA}[12w(2-w)D^2+R'] .
 \end{aligned}
\]
Here \(S_c\) multiplies \(P=\max(n,v)\), and \(T\) multiplies \(v\).
For the nominal shared width write
\[
 V=\min\left\{(1+x+y+z)(\sqrt{1+x}-\sqrt b)_+^2,\;
       (1+x)(\sqrt{1+x+y+z}-\sqrt{b(1+x+y)})_+^2\right\}.
\]
The paid squared width divided by \(b^2\) is \(cV\).
The common trace price is
\(T_s=n[1-\min(1/2,n/(3v))]\), with \(T_s=n/2\) at \(v=0\),
and zero at \(n=0\).
[Joint trace proof](rank7_joint_trace_prices.md)

With the geometric notation \(M=\max(n,v/2)\),
\(Z=\max(5n/2,2v,2n+v)\), \(J=(2n+v-3M)_+\),
\(B_1=\max(v,n/2)\), set
\[
 F=S_cP+Tv+96cVT_s/A+\rho D[(b-1)(c-1)B_1-v]+c\lambda'n .
\]
The split and singleton normalized margins are, respectively,
\[
 \begin{aligned}
 F_{\rm split}&=F+c(yv-H'n),\\
 F_{\rm single}&=F+c[z(M-xn)+(2y+3x)M]+Z/b^2
             +\min(x/b,cbC')\,J,\\
 C'&=x(z+y+x)(x+\rho y)-\lambda'(y+2x)\ge0 .
 \end{aligned}
\]
The final inequality follows from the allowed shifts and the
nonnegative completion coefficient in the original expansion.
The lower physical comparison and the signed exterior gain plus
the crossing allowance are affine in \(c\). For a given interval of
the ratio \(r=v/n\), check the two endpoints \(c=1,b\), using the
same \(f,u,w\) at both. At either endpoint one may choose its own
convex combination of \(F_{\rm split},F_{\rm single}\) on the
two boundary rays of that interval. The affine comparison then
holds for the same actual frame throughout \(1\le c\le b\).
For the \(r\) variable it suffices to use adjacent pairs of
\(0,1/2,2/3,1,2,4,\infty\); the only nonlinear term on each
sector is the concave shared trace price.

## Domain and exact traversal

The [checker](../verification/verify_rank7_tied_fourth_lower_fifth.cpp)
uses the fixed-scale checked integer arithmetic of the
[base interval implementation](../verification/verify_rank7_equal_fifth_sixth.cpp),
at scale \(2^{27}\) with signed 128-bit intermediates. All endpoint
rounding is outwards. Square-root endpoints are checked by integer
squaring. The two root differences use conjugate denominators and
the nonnegative parts of \(1+x-b\) and \(z-(b-1)(1+x+y)\) for their
numerators. The lower endpoint margins are strictly positive for
one common convex mixture exactly when the two linear half-intervals
for its mixing coefficient have intersecting strict interiors; the
code checks this using signed cross products.

The domain tests and contractions use \(b^2D<1800/61,\ b^2G<160\),
\(5G>z+2y+3x\), \(z>3/5,\ 96y>1,\ y<11/2,\ x<17,\ z<190\).
They may also discard the previously established
\(x+2y\le1\) pure exterior test and the two vanishing-width
branches. The alternative weighted-split certificate contains the
lower physical price
\[
 b^2\left\{[12w(2-w)D^2+R']/K+\max(G^2/24,x^4/72)\right\}
       +168y-(168-24w)D .
\]
Its strict positivity is sufficient for every \(c\ge1\) by
the [weighted residual](rank7_weighted_split_residual.md).

The slab boundaries, in the checker's descending order, are
\(4/3,5/4,6/5,23/20,11/10,21/20,101/100\). Each invocation
takes its inclusive first and last slab numbers. The frozen
source SHA-256 is
\(\texttt{d72da423795bc5d65354cffc07c08b9ca170938f43716ccaa44b5ab9fc5d8255}\);
the base source SHA-256 is
\(\texttt{db8df09e4e34c9f42953085f2363a43c6f152db5a1d9ee39be00b81ac3b8e71a}\).

~~~text
g++ -std=c++20 -O3 -o cb_tied_fourth_lower_fifth.exe verification/verify_rank7_tied_fourth_lower_fifth.cpp
./cb_tied_fourth_lower_fifth.exe 1 6
~~~

## Completed directed-arithmetic run

All six slabs completed with 503,922; 462,041; 689,806; 833,134;
954,522; and 907,143 accepted leaves, respectively. Maximum observed depth
was 34. See the [round record](rank7_seed_transfer_and_priority_round_2026-11-18.md)
for per-branch counts and persisted logs. Every accepted branch transmits
to arbitrary \(a-b\ge0\) by the [complete branch transfer](rank7_seed_branch_transfer.md).
With the older close-bottom theorem this covers every spectrum with
\(b\le4d/3\).
