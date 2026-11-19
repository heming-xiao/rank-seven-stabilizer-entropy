# Rank-seven optimality with three equal smallest probabilities

November 18, 2026. For every ordered positive Schmidt spectrum
proportional to \((\alpha,\beta,\gamma,a,d,d,d)\), the sorted
computational representative globally minimizes order-two nonlocal
stabilizer Rényi entropy over arbitrary complex local unitaries on
every qubit bipartition. The four remaining probabilities have
arbitrary ratios. In particular the generic five-level
multiplicity pattern \((1,1,1,1,3)\) is covered. Every fixed
spectrum in the family has a relative open rank-seven neighborhood
of optimality.

The proof keeps a new loss on the wedge containing the four
largest labels and otherwise extends the
[flat-four-tail proof](rank7_four_equal_tails.md). Normalizing by
\(d\), set \(d=1\). Define \(p=a-1\), \(h=\alpha-\beta\),
\(k=\beta-\gamma\), \(q=\gamma-a\),
\(X=h+k+q,\ Y=k+q,\ g=hq,\ \Delta=kX,\ J=Yq\).

## A retained spectral loss on the first four labels

Use the same-frame notation of the
[three-price expansion](rank7_three_price_head_expansion.md).
Let \(A_3=w_{0123}\), \(e=1-A_3\),
and \(x=1-\sum_{i=3}^6w_{012i}\).
The retained deficiency and the geometric bounds give
\[
 D_A=x+pe,\qquad e\ge P:=\max(n,v),\qquad
 n=\nu_+,\quad v=(L_{01}-2)_+ .
\]
The last inequality is the
[top-four projection bound](rank7_low_head_tail_prices.md).

At the tied-four-head auxiliary spectrum
\((a,a,a,a,1,1,1)\), consider an edge among the first three
labels. Among its five possible completion labels, precisely
two have weight \(a=1+p\). The reference contains one completion
with both of these labels and one completion with neither.
Expanding the completion weights gives
\[
 U_e^0=(L_e-2)-p[(1-T_{e,i})+(1-T_{e,j})]-p^2e ,
\]
where \(i,j\) are the two higher completion labels and
\(T_{e,i}\) is the three-leg occupancy that retains the edge
and label \(i\). Both three-leg occupancies are at most one.
Therefore the earlier weighted deficits obey
\(B_s\ge2p^2e,\ B_1\ge p^2e,\ B_\triangle\ge3p^2e\).

The pure fourth-gap quartic \(p^4\), and the monomials
with one leading gap and three factors \(p\), are supported only
on \(0123\). Their combined loss is exactly
\((p^4+Lp^3)e\), where \(L=h+2k+3q\).
They are separate from the \(d^4\delta N\) and singleton-head
terms with other gaps \(d^3\), so their losses can be retained
in addition. All other restored terms in the degree-zero and
degree-one head module are ordinary nonpositive coefficients.
[Separate singleton and tail terms](rank7_three_price_head_expansion.md)

Use \(b_*=(101/100)168\), \(s=5g/4\), \(t=5\Delta/4\), and
\(\lambda=24s/b_*,\ \mu=24t/b_*,\ \zeta=0\). Let
\[
 \begin{gathered}
 C=XYq-\lambda(Y+q)-\mu q,\qquad
 B_{\mathrm{top}}=p^4+Lp^3+pC+
           p^2[2(g-\lambda)+(\Delta-\mu)+3J],\\
 M=\max(n,v/2),\quad Z_N=\max(5n/2,2v,2n+v),\quad
 b_0=1-30/b_* .
 \end{gathered}
\]
Here \(C\ge(9/14)XYq\), since \(g(Y+q)+\Delta q\le2XYq\)
and the common price is less than \(5/28\). The part \(Cx\)
may be used in the geometric term, independently of \(pCe\).
Use \(H=3M\) throughout and
\(H=3M+(2n+v-3M)_+\) when \(9XY\ge14\).
The exterior packing requirement is then
\[
 E-\lambda U-\mu U_1
 \le b_0(gn+\Delta v)-(h+2k)M-qH-Z_N-B_{\mathrm{top}}P .
\tag{1}
\]
The stronger \(H\) follows from the same geometric interpolation
as in the three-price proof, with \(C x\) available, because
\(C\ge q\) when \(9XY\ge14\). The signed triangle term is
nonpositive and can be discarded.

## Physical payments and rational compression prices

Since \(b=c=d\), the original shared mixed price is \(G=g\).
The two shifts have nonnegative cross price
\((15/16)g\Delta\). As in the four-equal-tail theorem, the sum
of the actual mixed and anticommuting defects is at least
\[
 24sU+24tU_1+(49/4)g^2\kappa+
               [(45/4)\Delta^2+R]\kappa_1,\qquad
 R=k^2[k^2+(h^2+q^2)/2].
\]
Use \(\kappa\ge P/12,\ \kappa_1\ge v/(5/2)\).

For the highest-pair cut the inside minimum is \(\alpha\beta\)
and the outside maximum is \(\alpha\gamma a\).
For the shared cut these endpoints are \(\alpha\gamma\) and
\(\max(\alpha a,\beta\gamma a)\).
When a cut separates, use its adjacent gap in the nested
compression inequality. When both separate their gap intervals
are disjoint because \(\alpha\gamma\le\alpha\gamma a\).
For an unseparated cut the assigned contribution is zero.
The highest-pair trace gives the factor \(64v\) in the physical
comparison. The shared trace, on \(E>0\), gives
\[
 96n\frac{(f-\Delta/3)_+}{g+2f},\qquad f=aXYq,
\]
multiplying its squared amplitude gap.
[Nested compression](rank7_compression_slack_astra.md) ·
[Trace localization](rank7_uniform_cut_packing.md)

The score differences at these cut endpoints are
\(\alpha(k-p\gamma),\ \alpha q,\ \gamma(h-p\beta)\).
Use \((\sqrt u-\sqrt w)^2\ge(u-w)^2/[2(u+w)]\)
and \((x-y)_+^2\ge x(x-2y)\). This gives the following signed
lower bounds for the three possible squared gap prices:
\[
 \frac{\alpha k(k-2p\gamma)}{2(\beta+a\gamma)},\qquad
 \frac{\alpha q^2}{2(\gamma+a)},\qquad
 \frac{\gamma h(h-2p\beta)}{2(\alpha+a\beta)}.
\]
The first is for the highest-pair gap. The minimum of the last
two is for the shared gap. If either bound required for the
shared gap is negative, the true nonnegative compression term
still bounds its minimum. A positive signed price implies actual
separation. In using a shared signed price, certify
\(f-\Delta/3\ge0\) first. Cases \(q=0\) or coincident
thresholds follow by continuity of the physical comparison.

## Exact coverage of the scalar comparison

For any fixed spectrum, the sufficient comparison obtained
from (1) is linear in \((n,v)\) within the sectors bounded by
the axes and \(v/n=1/2,1,2,4\). It suffices to check those
six directions. In the comparison divided by \(b_*\), the
mixed and anticommuting contributions are
\((49/(48b_*))g^2P\) and
\(((45/4)\Delta^2+R)v/((5/2)b_*)\).
The nonnegative \(B_{\mathrm{top}}P\) can be retained
separately with the geometric loss.

For \(L\ge33\), the same completed-square argument as for
four equal tails pays the exterior gain without compression.
It also applies to the extra direction \((1,4)\).
For \(L\le33\) and \(p\ge9/4\), pure exterior overlap suffices:
\[
 E\le gn+\Delta v-Lp^3P\le0 ,
\]
using \(g\le L^2/12,\ \Delta\le L^2/4\),
and \(p^3\ge33/3\).
So the remaining region is covered by the unit cube with
\((h,k,q,p)=(33u_1,(33/2)u_2,11u_3,(9/4)u_4)\).

The [exact verifier](../verification/verify_rank7_three_equal_tails.py) checks
this region by dyadic Bernstein subdivision with integral
coefficients after clearing positive denominators. It accepts a
box if the base inequality holds, if the base plus the highest
cut holds, or if both shared alternatives hold with the trace
numerator nonnegative. It may use the stronger \(H\) only when
the same box certifies \(9XY\ge14\).
The six exact trees total 281 leaves at maximum depth 15.

This proves \(b_*E\le P_{\mathrm{Pauli}}+96\mathcal D_F\)
on \(E>0\), retaining at least \(1/101\) of the actual defect
sum. On \(E\le0\) all nonnegative actual defects remain.
The exact paired reduction, stabilizer padding and
strict-margin transfer give all stated cuts and neighborhoods.
[Paired purity and compression](https://arxiv.org/html/2609.13106v2) ·
[Strict transfer](rank7_open_interior_neighborhood.md)
