# An explicit compact region for the remaining rank-seven spectra

November 18, 2026. For every ordered positive Schmidt spectrum
\((\alpha,\beta,\gamma,a,b,c,d)\), let
\(S=(\alpha-\beta)+2(\beta-\gamma)+3(\gamma-a)\). On any qubit
bipartition, the sorted computational representative is globally optimal
at order two if
\[
  bcS\;\ge\; 3A c^2d+7d^3,\qquad A=(101/100)\,168. \tag{1}
\]
In particular \(S\ge517d\) suffices, with no condition on tail
ratios. The proof retains the paired margin of \(1/101\).
Together with the pure exterior comparisons, this confines every
remaining case to \(d/\alpha>1/1057\).

## One mixed shift and unweighted anticommuting loss

Normalize \(d=1\). Write \(h=\alpha-\beta\), \(k=\beta-\gamma\),
\(q=\gamma-a\), \(X=h+k+q\), \(Y=k+q\), \(g=hq\),
\(\Delta=kX\), \(p=a-b\). Let \(n\) and \(v\) be the positive parts of
the shared and highest-pair excesses, and put
\(P=\max(n,v)\), \(M=\max(n,v/2)\). With the single highest-pair
mixed shift \(t=5\Delta/4\), choose \(\mu=24t/A=30\Delta/A\) and
\(\lambda=\zeta=0\) in the three-probe exterior inequality. Its
completion coefficient is \(XYq-\mu q\ge0\), since
\(\Delta\le XY\) and \(30/A<1\).
The universal tail-weighted singleton loss is \(bcSM\).
Dropping the other nonpositive terms gives
\[
       E-\mu U_1\le cgn+(\Delta-\mu)v-bcSM. \tag{2}
\]
[Three-probe exterior inequality](rank7_low_head_tail_prices.md).

The highest mixed projection contributes
\(24tU_1+(45/4)\Delta^2\kappa_1\). The independent anticommuting
loss contributes at least \(g^2\kappa+\Delta^2\kappa_1/5\).
The bounds \(\kappa\ge P/12\), \(\kappa_1\ge v/(5/2)\)
use the same physical frame. These comparisons hold for the
entire ordered domain. [Single mixed shift](rank7_two_probe_separation_and_tail_region.md) · [Anticommuting loss](rank7_two_probe_anticommuting.md) · [Probe bounds](rank7_uniform_cut_packing.md).

With \(D\) denoting the sum of the actual mixed and anticommuting
losses, subtract \(AE\), use (2), and divide by \(A\).
Completing the square in \(g\) gives a debit no larger than
\(3Ac^2n^2/P\), interpreted as zero at \(P=0\).
Completing the square in \(\Delta\) gives a debit at most \(7v\)
since
\[
  \frac{(1-30/A)^2(5/2)A}{4(45/4+1/5)}<7.
\]
Thus it suffices to pay \(3Ac^2n^2/P+7v\) with \(bcSM\).

When \(M>0\) the debit divided by \(M\) is at most \(3Ac^2+7\).
For \(v\le n\), use \(P=M=n\). For \(v\ge2n\), use
\(P=v\), \(M=v/2\), and obtain at most \(3Ac^2/2+14\).
For \(n\le v\le 2n\) with \(n>0\), the ratio is
\(3Ac^2/r+7r\) for \(r=v/n\), which is convex and hence bounded by
its largest endpoint. The \(v=0\) and \(n=0\) axes already lie
in the first and second cases. Because \(3A/2>7\), the larger
endpoint is \(3Ac^2+7\), as claimed. This proves \(D\ge AE\)
under (1) at \(d=1\). The exterior gain enters the purity difference
with coefficient \(168\), so on \(E>0\) this retains \(D/101\) and the
full compression loss. On \(E\le0\) the full actual defect is retained.
Homogeneity restores \(d\) in (1). Since \(b\ge c\ge1\),
\(bcS\ge c^2S\), and \(3A+7=516.04<517\).

## Restricting the domain still to prove

With \(d=1\), (1) covers \(S\ge517\). The pure exterior condition
\(q+2k/c\le b\) covers \(b\ge S\), and the fourth-gap condition
\(p(p+q)\ge c\) covers \(p^2\ge c\).
Every remaining point therefore has
\[
   c\le b<S<517,\qquad p<\sqrt c<23,\qquad
   \alpha=b+p+X<517+23+517=1057 .
\]
After normalization by \(\alpha\), the entire unresolved domain
is within the closed compact region with smallest probability at
least \(1/1057\). On it one can use the common cutoff
\(\delta(1/1057)\) in the low-defect theorem. The remaining task is
to control the larger-defect comparison on that domain.
[Low-head exterior condition](rank7_low_head_tail_prices.md) · [Fourth-gap condition](rank7_fourth_gap_lift.md) · [Low-defect cutoff](rank7_low_defect_interior.md).

