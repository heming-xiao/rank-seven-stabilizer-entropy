# Separating two mixed probes and a rank-seven spectral region

November 18, 2026. Let the seven ordered positive probabilities be
\((\alpha,\beta,\gamma,a,b,c,d)\). Write
\[
 h=\alpha-\beta,\quad k=\beta-\gamma,\quad q=\gamma-a,\quad
 g=hq,\quad m=\alpha-a=h+k+q,\quad \Delta=km,\quad T=b+c-d.
\]
The sorted computational representative is globally optimal at order
two on arbitrary qubit bipartitions whenever
\[
 \alpha-a\ \le\ \tfrac75(b+c-d).
\]
Every fixed spectrum in this region has a full relative open
neighborhood of optimality, including on the boundary of the inequality.
The proof also gives a decomposition of the actual mixed defect that
applies to arbitrary spectra.

## Keep both mixed probes in one norm bound

Follow the [joint mixed polarization](rank7_general_two_probe_matching.md):
let \(u\) be the shared probe and \(u_1\) the highest-pair probe, with
\(\kappa=2\|u\|^2\), \(\kappa_1=2\|u_1\|^2\), and
\(c_1=2\langle u,u_1\rangle\ge0\). Write \(U=W-W_*\),
\(Y=W_1-W_{1,*}\), and \(L=L_-(C)\). The two probes give
\[
 2\langle u,L\rangle\ge H_{\rm sh}+\Delta c_1,\qquad
 2\langle u_1,L\rangle\ge Y+\Delta\kappa_1+g c_1 .
\]
For the second inequality, multiply the full conditioned matching
bound by \(p_{01}\) and average. Its \(g(1-p)\) term has average
\(gc_1\). The other two decreases are nonnegative and can be
omitted. In the first inequality one can take the lower bound
\(H_{\rm sh}=G\kappa+U\), where \(G=g-\lambda(b^2-cd)\le g\)
with the same \(\lambda\) as in the tied-middle proof.

For any \(s,t\ge0\), expand the nonnegative square
\(\|L-su-tu_1\|^2\). The single actual mixed contribution satisfies
\[
 24\|L\|^2\ge 24sH_{\rm sh}-12s^2\kappa+
 24tY+12(2t\Delta-t^2)\kappa_1
 +24(s\Delta+tg-st)c_1 .
\]
If shared gain needs payment, use \(s=(H_{\rm sh})_+/\kappa\);
otherwise use \(s=0\). In the first case \(U\le cd\,\nu\le12cd\,\kappa\),
and positive shared gain forces \(g>16b^2\), as shown below.
Thus \(s\le g+12cd<2g\).
At \(\kappa=0\) the shared probe is zero and we take \(s=0\).
For these choices the cross coefficient \(s\Delta+tg-st\)
is nonnegative on \(0\le t\le2\Delta\), since it is affine in \(t\)
and nonnegative at both endpoints. In particular \(t=2\Delta\)
supplies \(48\Delta Y\) while keeping the complete shared
mixed contribution in its positive branch.
The [independent anticommuting estimate](rank7_two_probe_anticommuting.md)
provides an additional \(g^2\kappa\), plus
\(\eta_1\kappa_1\) with
\(\eta_1=k^2[k^2+(h^2+q^2)/2]\).

## Absorb the shared change and control the highest pair

At the tied-middle spectrum \((\alpha-k,\gamma,\gamma,a,b,c,d)\)
in the same frame, let \(E_0,U_0\) be the normalized exterior gain
and the shared weighted difference. Write \(E\) for the actual
normalized exterior gain and \(D_A=a-\sum_{j=3}^6t_jw_{012j}\ge0\).
The [weighted comparison for raising the two leading probabilities](rank7_leading_split_packing.md)
gives \(U=U_0-kD_A\), and its weighted prefix inequality gives
\[
 E-E_0\le k(m-T)Y-kq(\gamma+a-d)D_A .
\]
The [strengthened cubic comparison](rank7_highest_pair_split_loss.md)
also gives \(E-E_0\le kmY\).
Put \(A_*=\gamma+a-d\). It satisfies \(A_*\ge T>0\).

If \(m\le T\), take a convex combination of the two bounds, with
weight \(m/T\) on the first displayed bound. This cancels \(Y\)
and gives \(E-E_0\le -k(m/T)q A_*D_A\le-kgD_A/2\).
If \(T<m\le7T/5\), then \(h\le m<2A_*\), so the prefix
bound gives
\[
 E-E_0\le k(m-T)Y-kgD_A/2,\qquad
 0<k(m-T)\le2\Delta/7 .
\]
For \(Y\le0\) drop its nonpositive contribution and use \(t=0\).
For \(Y>0\), the gain in purity priced at 168 is at most
\(48\Delta Y\) on this term. It is covered by the mixed estimate
at \(t=2\Delta\), leaving the shared comparison intact.

For the shared part let \(\nu=L_{01}+L_{02}-4\) and \(S=cd\).
If \(\nu\le0\), \(E_0\le0\) by the forward-gap bound and the
whole adjustment \(-kgD_A/2\) is nonpositive. If \(\nu>0\), the
[tied-middle weighted packing bound](rank7_equal_middle.md)
gives \(U_0=S\nu-B_0\), \(E_0\le SH\nu-gB_0/2\),
with \(H=g-b(h+3q)-5b^2/2\) and \(B_0\ge0\).
The actual shared deficit is \(B=B_0+kD_A\ge0\). Thus
\(E_0-kgD_A/2\le SH\nu-gB/2\), precisely the same comparison
as for tied middle on setting \(U=S\nu-B\).
In the positive part of that bound, the tied-middle scalar proof
applies with the same \(g,H,S\) and the same six-mode correction.
The term \(12(H_{\rm sh})_+^2/\kappa\) plus \(g^2\kappa\)
covers it strictly. When the bound is nonpositive the shared
payment can be omitted.

The strict comparison in the positive shared branch leaves a
spectrum-dependent positive excess proportional to \(\nu\).
In the positive highest-pair branch the unused
\(\eta_1\kappa_1\) is positive and \(Y\le4d^2\kappa_1\).
Together these bounds allow a uniform positive fraction of the
actual total defect to be retained at each fixed spectrum.
When neither bound is positive the exterior gain is nonpositive.
The [strict-margin transfer](rank7_open_interior_neighborhood.md),
paired comparison, and stabilizer padding give the claim on all cuts.

For example the strictly ordered spectrum proportional to
\((1,99/100,3/4,12/25,8/25,3/10,1/20)\) is strictly inside the
displayed region. It fails the two
[earlier tail and inverse-gap conditions](rank7_unbounded_spread.md)
\(\alpha\le3b\) and \(1/a\le1/\alpha+1/\beta\).
