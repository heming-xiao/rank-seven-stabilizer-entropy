# Rank-seven optimality with the smallest three probabilities within one percent

November 18, 2026. For positive sorted Schmidt probabilities
\((\alpha,\beta,\gamma,a,b,c,d)\), the sorted computational
representative minimizes order-two nonlocal stabilizer Rényi entropy
over all complex local unitaries and every qubit bipartition if
\[
                             b\le (101/100)d .
\]
The first four ratios are unrestricted. The comparison retains at
least \(1/101\) of the full paired defect sum throughout the closed
region, including its endpoint. In particular every fixed positive
spectrum in it has an unrestricted relative open neighborhood of
optimality. The theorem enlarges the [three-equal-tail family](rank7_three_equal_tails.md)
and permits all seven probabilities to differ.

## Exterior losses that survive splitting the three smallest probabilities

Normalize \(d=1\). Use \(p=a-b,\ h=\alpha-\beta,\ k=\beta-\gamma,\
q=\gamma-a,\ X=h+k+q,\ Y=k+q,\ L=h+2k+3q,\ g=hq,\ \Delta=kX,\
J=Yq,\ F=XYq\). For normalized wedge occupancies \(w_I\), set
\(x=1-\sum_{i=3}^6w_{012i}\) and \(e=1-w_{0123}\).
Let \(n=(L_{01}+L_{02}-4)_+\), \(v=(L_{01}-2)_+\),
\(P=\max(n,v)\), \(M=\max(n,v/2)\), and
\(Z_N=\max(5n/2,2v,2n+v)\). The top-four row gives \(e\ge P\).
Let \(E\) be the normalized exterior gain and \(U,U_1\) the weighted
shared and highest-pair probe differences, all from the sorted
computational frame. [Top-four bound and weighted singleton prices](rank7_low_head_tail_prices.md)

In the auxiliary tied-four-head frame let \(B_s,B_1,B_\triangle\)
denote its shared, first-pair and triangle weighted deficits. For
every ordered four-tail tuple,
\[
 D_A\ge bx+pe,\qquad
 B_s\ge2p^2e,\qquad B_1\ge p^2e,\qquad B_\triangle\ge3p^2e. \tag{1}
\]
Indeed \(D_A=ax+\sum_{i=3}^6(a-r_i)w_{012i}\) for
\(r=(a,b,c,1)\). The three indices \(i\ge4\) have total
occupancy \(e-x\) and \(a-r_i\ge p\). In the six-row
decomposition of \(B_s\), the coefficient of \(x\) is
\(ap+(a-c)(a-1)\ge2p^2\), and each coefficient on \(w_{012i}\)
for \(i\ge4\) is \((a-r_i)(2a+r_i-b-c-1)\ge2p^2\).
For \(B_\triangle\), one of its nonnegative summands is
\((3a-b-c-1)D_A\ge3p^2e\). For \(B_1\) the sorted five possible
completion labels have weights \((a,a,b,c,1)\). The directed prefix
deficits are all nonnegative except the full prefix squared, which
has already supplied the unweighted trace. The length-two prefix
has gap \(p\); its diagonal term supplies exactly \(p^2(1-w_{0123})\).
[Six shared and triangle rows](rank7_three_price_head_expansion.md) ·
[Five-label prefix rows](rank7_equal_highest_pair_cone.md)

Set \(b_*=(101/100)168\), \(\rho=30/b_*\), \(r=1-\rho\),
\(G=(g-(200/11)b(c-1))_+\), and take the physical mixed shifts
\(s=5G/4,\ t=5\Delta/4\), with exterior prices
\(\lambda=\rho G,\ \mu=\rho\Delta\).
The signed three-head completion price is
\(C=F-\lambda(Y+q)-\mu q\ge C_0:=F-\rho[g(Y+q)+\Delta q]
\ge(9/14)F\).
Keep
\[
 T=p^4+Lp^3+p C_0+p^2[2rg+r\Delta+3J].
\]
The pure \(p^4\) term and singleton \(Lp^3\) term each occupy
only wedge \(0123\) and supply their coefficients times \(e\);
the other terms in \(T\) follow from (1). The singleton coupons
for the nonconstant monomials in \(bc-1\) give an additional
\(L(bc-1)M\). These coupons have at least one tail-gap index 4
or 5; the \(Lp^3\) coupon has only tail-gap index 3. The
geometric \(L M\) term is paid by the constant tail product
and uses only tail-gap index 6. This separation permits retaining
all three. The \(bx\) in (1) covers the same geometric interpolation
as in the tied-three proof because \(b\ge1\). In particular it
also supplies \(I=q(2n+v-3M)_+\) when \(9XY\ge14\); use \(I=0\)
otherwise. Thus the signed comparison is
\[
 E-\lambda U-\mu U_1\ \le\
   c(g-\lambda)n+r\Delta v
       -LbcM-Z_N-TP-I. \tag{2}
\]
[Disjoint forward coupons](rank7_low_head_tail_prices.md) ·
[Geometric interpolation](rank7_uniform_cut_packing.md)

## Uniform physical comparison on two overlapping endpoint cases

Write \(u=101/100\). Choose \([\ell,z]\) as either
\([1,201/200]\) or \([201/200,101/100]\) so that \(c\in[\ell,z]\).
Set \(\tau=(200/11)u(z-1)\) and \(R=k^2[k^2+(h^2+q^2)/2]\).
The mixed-square cross coefficient is nonnegative, as in the
previous unequal-tail comparison. The two actual Pauli defects
pay \(b_*(\lambda U+\mu U_1)\) and at least
\([g^2+(45/4)G^2]P/12+[(45/4)\Delta^2+R]v/(5/2)\) beyond it.
Using \(G^2\ge g^2-2\tau g,\ G\ge g-\tau\), and \(bc\ge\ell^2\),
a conservative lower bound on the combined price minus \(E\),
before compression and divided in physical units by \(b_*\), is
\[
 B=L\ell^2M+Z_N+TP+I+
   \frac{(49/4)g^2-(45/2)\tau g}{12b_*}P+
   \frac{(45/4)\Delta^2+R}{(5/2)b_*}v
        -z(rg+\rho\tau)n-r\Delta v . \tag{3}
\]
[Mixed and anticommuting bounds](rank7_four_equal_tails.md)

For \(E>0\), the two nested cuts can supply \(64v\) times the
highest-pair squared gap and \(96n\omega\) times the shared squared
gap, in physical units. An unseparated cut supplies zero. The
inside and outside endpoints are \((\alpha\beta c,\alpha\gamma ab)\)
and \((\alpha\gamma c,\max(\alpha abc,\beta\gamma ab))\).
When both intervals separate, \(\alpha\gamma c\le\alpha\gamma ab\)
makes their contributions distinct. The trace ratio obeys
\[
 \omega=\frac{(aF-\Delta/3)_+}{cg+2aF}
   \ \ge\ \frac{(a_-F-\Delta/3)_+}{zg+2a_-F},\qquad
      a_-=\ell+p,\quad a_+=u+p .
\]
It is increasing in \(aF\) and decreasing in \(cg\). A zero
denominator is assigned zero. [Shared trace bound](rank7_uniform_cut_packing.md) ·
[Nested compression](rank7_compression_slack_astra.md)

Define \(\alpha_\pm=a_\pm+X,\ \beta_+=a_++Y,\
\gamma_\pm=a_\pm+q,\ A=(u/\ell)a_+\), and \(\theta=A-1\).
Three signed lower bounds on the squared amplitude gaps are
\[
 \begin{split}
 H_1&=\frac{\ell\alpha_-\,k(k-2\theta\gamma_+)}
                         {2(\beta_++A\gamma_+)},\\
 H_2&=\frac{\ell\alpha_-\,q(q-2a_+(u-1))}
                         {2(\gamma_++u a_+)},\\
 H_3&=\frac{\ell\gamma_-\,h(h-2\theta\beta_+)}
                         {2(\alpha_++A\beta_+)} .
 \end{split} \tag{4}
\]
For example, divide the first score pair by \(\alpha c\). Its
difference is \(\beta-\gamma ab/c\ge k-\theta\gamma_+\), and its
sum is at most \(\beta_++A\gamma_+\). For the shared left endpoint
the reduced difference is \(\gamma-ab=q-a(b-1)\); the shared right
endpoint has \(\alpha-\beta ab/c\ge h-\theta\beta_+\). In all cases
apply \((\sqrt{y}-\sqrt{z})_+^2\ge (y-z)_+^2/[2(y+z)]\)
and \((s-t)_+^2\ge s(s-2t)\) for nonnegative \(s,t\).
When a displayed right side is negative the actual payment is
nonnegative. The minimum of \(H_2,H_3\) is valid for the shared cut;
both signed sides must be checked. [Rational gap comparison](rank7_near_equal_tails.md)

## Exact whole-region certificate

For \(L\ge35\) the existing [outer square certificate](rank7_four_equal_tails.md)
already allows \(b\le101/100\) with arbitrary fourth entry.
Independently, when \(p\ge u\), pure exterior packing pays the
gain without either cut. Indeed \(D_4=(p+X)(p+Y)(p+q)p
\ge p^2 XY\), \(XY-(g+\Delta)=qY\ge0\), and \(p^2\ge u\ge c,1\).
The top-four coupon therefore covers \(cgn+\Delta v\) by \(D_4P\).
[Pure top-four coupon](rank7_low_head_tail_prices.md)

In the remainder set \((h,k,q,p)=(35z_1,(35/2)z_2,(35/3)z_3,uz_4)\)
on the unit four-cube. On each of the two allowed \(c\)-intervals
all bounds (3) and (4) are rational functions in these four variables.
For a fixed spectrum their sufficient comparison is linear on each
sector between the axes and \(v/n=1/2,1,2,4\). The verifier checks
these six boundary rays for both intervals. It can use (3) alone,
(3) with the first cut, or either one with the shared cut after
certifying \(a_- F-\Delta/3\ge0\) and both shared alternatives.
A box uses the increment \(I>0\) only after certifying \(9XY\ge14\)
there. The \(H_2\) alternative cancels one factor \(q\) from its
numerator and the trace denominator; zero gaps are covered by
continuity of the original physical comparison.
[Exact verifier](../verification/verify_rank7_near_three_tails.py)

After clearing positive denominators, tensor Bernstein subdivision
using rational arithmetic and scaled integers gives the following
counts. An outer leaf has \(L\ge35\) throughout.

| Interval for \(c\) | Comparison leaves | Outer leaves | Maximum depth |
|---|---:|---:|---:|
| \([1,201/200]\) | 333 | 37 | 18 |
| \([201/200,101/100]\) | 325 | 37 | 18 |

Hence \(b_* E\) is paid by the sum of the Pauli and compression
defects on every frame with \(E>0\); for \(E\le0\) all those defects
remain. The single-frame comparison thus retains at least the claimed
\(1/101\) of their sum. The paired reduction, stabilizer padding,
and strict transfer give the stated entropy comparison and open
neighborhoods. [Single-frame reduction](rank7_compression_slack_astra.md) ·
[Strict transfer](rank7_open_interior_neighborhood.md)

