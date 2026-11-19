# Transferring all branches of a fourth–fifth seed certificate

The data \(h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a,\
b,c,d\) are fixed and \(p=a-b\ge0\) varies. The comparison
at \(p=0\) may arise from the mixed-cut comparison, an older
exterior region, or a weighted highest residual. This note
shows how the non-mixed branches used by the exact verifiers
also transfer. In particular one need not assume that every
accepted box supplies a mixed-cut certificate.

## A weighted residual using the true highest cut

Normalize \(d=1\). Put \(X=h+k+q,\ \Delta=kX,\ b\le2\).
Write \(M_t(p)\) for left side minus right side of (1) in
the [weighted residual test](rank7_weighted_split_residual.md),
and \(W_1(p)=\sigma(p)^2\) for its actual highest squared width.
For fixed \(t\), \(\rho=1-t/(7\Delta)\). The change is exactly
\[
\begin{split}
 M_t(p)-M_t(0)={}&64[W_1(p)-W_1(0)]
     +168\rho\Delta p(a-c)\\
 &+168pkq[\rho X+q+3a-b-c-1-h/2].
\end{split}
\]
If \(k=0\) the earlier tied-middle theorem suffices. Otherwise,
using \(3a\ge b+c+1\), the positive change in exterior prices
per \(pk\) is at least
\[
             168(\rho-1/2)qX+84qk+252q^2 .
\]
For the highest true width the derivative estimate from the
[fourth-gap proof](rank7_true_cut_gap_ray.md) gives
\[
 64[W_1(0)-W_1(p)]\le r\, pk (c/b)(b+X),\qquad r=343/10 .
\]
Here \(64(4-2\sqrt3)<r\). If the seed width is zero, its
change cannot create a loss in this comparison.

For \(q\ge2/3\) and \(t\le5\Delta/4\), the first exterior term
is at least \(36X\); the last is at least \(112\).
These exceed \(r(X+b)\) for every \(b\le2\).
Thus the same weighted test transmits all the way along the
ray, including the true highest cut.

For \(4/3\le b\le2,\ q\ge\max(2/3,b/2)\), the same conclusion
holds at \(t\le3\Delta/2\). The three exterior terms are
at least \(48qX+84qk+252q^2\). If \(48q\ge r c/b\), the
term in \(X\) pays the corresponding width loss, and
\(252q^2\ge112>r b\) pays its remaining constant.
In the only other relevant case the seed width is positive
and \(48q<r c/b\). Then
\[
 \frac{c}{b}>\frac{320}{343},\qquad
 b<\frac{343}{240},\qquad
 c>\frac{1280}{1029},\qquad
 k>(b+q)(b-1)\ge\frac23 .
\]
The last inequality uses \((b+q+k)c>(b+q)b^2\)
from positivity of the true height at \(p=0\).
If \(\Delta\ge (1800/61)D_0(0)\), with
\(D_0(0)=1-(b-1)(c-1)\), the compression-free weighted
test at \(t=\Delta\) already covers every \(p\).
Indeed \(D_0(p)\le D_0(0)\) and
\([12\Delta^2+R]/(5/2)\ge(122/25)\Delta^2\).
Otherwise
\[
      X<\frac{2700}{61}\frac{2836}{3087}.
\]
The possible unpaid \(X\)-coefficient is at most \(r-32\).
The exact comparison
\[
 (r-32)\frac{2700}{61}\frac{2836}{3087}
       <112+\frac{112}{3}-\frac{r^2}{24}
\]
shows that the remaining \(qk,q^2\) terms pay that deficit
and the constant width loss. This proves the longer shift
transfer throughout the stated range. A compression-free
weighted seed needs neither of these width arguments:
its right side only decreases with \(p\).
[Exact constants](../verification/verify_rank7_seed_branch_transfer.py).

## Older domain and mixed-cut branches

The coordinate contractions for a potentially violating
spectrum can use \(D_0(0)\) in place of \(D_0(p)\), since
\(D_0(p)\le D_0(0)\). The necessary compact head bounds
on \(h,k,q,\Delta,g\) apply to the actual spectrum.
All earlier criteria that depend only on the five fixed
data apply directly at arbitrary \(p\). The pure exterior
criteria \(\alpha_0\le3b\) and
\(\alpha_0\beta_0\le b(\alpha_0+\beta_0)\) give \(E(0)\le0\).
The unpriced fourth-gap monotonicity gives \(E(p)\le E(0)\).
The no-shift harmonic transport criterion follows when
\(XD_0(0)\le bcd\), since \(D_0(p)\le D_0(0)\) and its
extra \(p\) term is nonnegative. The seed's two nominal
shared gap inequalities stay inactive separately:
each signed difference \(\alpha d-\beta b,\gamma d-ab\)
decreases by \(p(b-d)\) from the seed. Hence the two
zero-width cases remain in the proved region.
[Pure exterior criteria](rank7_unbounded_spread.md) ·
[Unpriced monotonicity](rank7_fourth_third_product.md) ·
[Harmonic transport](rank7_harmonic_tail_transport.md) ·
[Zero nominal shared width](rank7_zero_shared_width.md).

The remaining accepted branch supplies the signed
mixed-cut seed with its explicit nominal crossing allowance.
The [mixed-cut transfer](rank7_mixed_cut_full_fourth_ray.md)
supplies the same comparison along \(p\) for \(q\ge2d/3\);
a zero highest price is permitted. Its mixed remainder
remains available when increasing \(p\), since the estimate
uses the same upper bound \(b(c-d)\) on the six-mode
correction and all lower anticommuting payments retain
only the unchanged gap data. The trace lower prices
are functions of the frame alone.
Thus a completed slab with the stated branch checks
proves all spectra in that slab, not just the tie.

