# A uniform shared-anchor geometric bound and the rank-seven 1+2+4 family

November 17, 2026. For every physical shared-anchor frame, the two
geometric excesses satisfy
\[
 (L_{01}+L_{02}-4)_+ \le 16\kappa.
\]
Together with the [exact 1+2+4 scalar comparison](rank7_three_level_124_packing_and_scalar.md),
this proves global optimality for every spectrum proportional to
\((1,r,r,s,s,s,s)\), \(1\ge r\ge s>0\), on every qubit bipartition.
Every such spectrum has a full relative open rank-seven neighborhood.

## A fixed five-form estimate near a four-point affine block

Let \(D\) be any rank-four stabilizer block, so after a Clifford it is
the coordinate span of an affine four-point plane. Let \(\alpha\)
be a decomposable unit two-form, and \(Y\) any five-dimensional subspace
with unit volume form \(\Omega\). On two-forms define the positive
operator \(M_Y\) by
\[
 \langle\alpha,M_Y\alpha\rangle
 =q^{-1}\sum_{i<j}\|\Pi_F(\alpha\wedge y_i\wedge y_j)\|^2
\]
for any orthonormal basis of \(Y\), with \(q=4/d\). The one-hole
identity gives \(M_Y\preceq(5/2)I\) by summing over the second tail
in a complete orthonormal basis. Therefore \(L=2I-M_Y\) is between
\(-I/2\) and \(2I\), and \(\|L-3I/4\|\le5/4\).

For a general five-form \(\Xi\), define
\(\langle\alpha,L_\Xi\alpha\rangle
=2\|\alpha\|^2\|\Xi\|^2-\langle\Xi,A(\alpha)\Xi\rangle\),
where \(A(\alpha)\) is the five-particle lift of the two-tail positive
operator constructed from \(q^{-1/2}\iota_\alpha\psi_L\).
At \(\Xi=\Omega\) this is \(L\). If a decomposable \(\alpha\) lies in
an affine eight-point block, \(L_\Xi[\alpha]\ge0\) for every \(\Xi\).
The [affine-eight operator bound](reviews/rank7_two_link_independent_review.md)
applies first to the pair complement. On the full exterior space,
split by occupancy of the pair. The tail contractions act only on its
complement, so each resulting \(k\)-particle bound is at most
\(\lfloor k/2\rfloor\le2\) for \(k\le5\).

Use principal-angle bases for the plane of \(\alpha\) and \(D\).
Write
\[
 \alpha=c\alpha_0+\eta_1+\eta_2+\zeta ,
\]
where \(\alpha_0\) uses both reference legs in \(D\), each \(\eta_i\)
uses one reference leg and one orthogonal outside leg, and \(\zeta\)
uses two outside legs. The phase can make \(c\ge0\). These four
terms are pairwise orthogonal, and for the total squared leakage
\(E=\operatorname{Tr} P_{\mathrm{plane}(\alpha)}(I-P_D)\) one has
\(\|\eta_1\|^2+\|\eta_2\|^2\le E\) and \(\|\zeta\|\le E/2\).

Let \(\delta=L[\alpha_0]\ge0\) and partition the coordinate space into
the parallel four-point blocks of \(D\), with \(D\) designated color
zero. Split \(\eta_i=\sum_{b\ne0}\eta_{ib}\) by the outer leg's color.
The span of \(\alpha_0,\eta_{ib}\) consists of decomposable forms in
the eight-point union of blocks \(0,b\), since both terms share one
leg. Thus \(L_\Xi\) is positive on this span for every \(\Xi\).
Only projected plane directions meeting both color \(0\) and \(b\)
can contribute a cross term between \(\alpha_0\) and \(\eta_{ib}\).
Their reference tail pairs have color type \((b,b)\) and their
varied tail pairs have type \((0,b)\). Both sides of the lifted
operator have at least one particle in \(b\). Hence if \(\Omega_b\)
projects \(\Omega\) onto that occupancy sector, then
\(\langle\alpha_0,L_\Omega\eta_{ib}\rangle
=\langle\alpha_0,L_{\Omega_b}\eta_{ib}\rangle\).

The operator \(D_0=2I-A(\alpha_0)\) is positive and commutes with the
color occupancies, since each reference two-tail contraction is wholly
in one color. By Cauchy–Schwarz for the positive restriction to
\(\operatorname{span}(\alpha_0,\eta_{ib})\),
\[
 |\langle\alpha_0,L_{\Omega_b}\eta_{ib}\rangle|
 \le \sqrt{2}\|\eta_{ib}\|\|\Omega_b\|
    \sqrt{\langle\Omega_b,D_0\Omega_b\rangle}.
\]
The sum of occupancy projections over \(b\ne0\) is bounded by \(5I\).
Therefore
\[
 |\langle\alpha_0,L(\eta_1+\eta_2)\rangle|
 \le \sqrt{10}(\|\eta_1\|+\|\eta_2\|)\sqrt{\delta}
 \le \sqrt{20E\delta}.
\]
Complete the square using \(c^2\delta-2c\sqrt{20E\delta}\ge-20E\).
The remaining diagonal term of \(\eta_1+\eta_2\) is at least \(-E/2\).
For \(\zeta\), use \(\|\zeta\|\le E/2\), the centered operator bound
\(5/4\) on its cross term with the orthogonal rest, and \(E\le2\).
The cross and diagonal terms are at least \(-5E/4\) and \(-E/4\),
respectively. This proves
\[
 \langle\alpha,M_Y\alpha\rangle-2\le22E .
\]
The proof fixes \(Y\) even as it decomposes the pair. No
orthogonality of \(Y\) to the projected pair was assumed.

## Leakage estimates from the Fourier rounding

Use the [shared-anchor Fourier rounding](rank7_shared_anchor_fourier_rounding.md).
For \(\kappa<1/32\) it gives distinct parallel rank-two codes \(Q,Q'\)
with leakages
\[
 e_M=2-\operatorname{Tr}(P_M P_{Q'})\le10\kappa,\qquad
 e_x=1-\|P_Qx\|^2
 \le\frac{5\kappa}{2(1-10\kappa)^2}.
\]
Its Fourier bootstrap further gives \(e_M+2e_x<1/10\).
Let \(\mathcal C\) be the \(d\) skew Pauli labels whose syndrome sends
\(Q\) to \(Q'\). They span exactly the exterior-square sector
pairing each code with its partner by that syndrome. Write
\(\tau=(\sqrt{e_M}+\sqrt{e_x})^2\le(3/2)(e_M+2e_x)<3/20\).
For \(a\notin\mathcal C\), \(J_aQ\perp Q'\), so \(p_a\le\tau\).
For \(a\in\mathcal C\), \(J_aQ=Q'\) and
\[
 \|P_M J_a x\|\ge \sqrt{(1-e_x)(1-e_M)}-\sqrt{e_xe_M},
 \qquad p_a\ge1-\tau .
\]
The first term uses the smallest squared singular value of
\(P_M|_{Q'}\), at least \(1-e_M\). The error term follows since
\(J_a(Q^\perp)=Q'^\perp\), where the projection onto \(M\) has
norm at most \(\sqrt{e_M}\).

With normalized skew sums \(2/d\), the lost mass
\(\ell=2-\langle 1_{\mathcal C}p\rangle\) equals both
\(\langle 1_{\mathcal C}(1-p)\rangle\) and
\(\langle 1_{\mathcal C^c}p\rangle\). The pointwise bounds imply
\(\kappa\ge2(1-\tau)\ell\). Now put \(D=Q\oplus Q'\) and let \(e'_x,e'_M\)
be the squared leakages of \(x,M\) out of \(D\).
The sector of \(\mathcal C\) lies in the exterior squares of the paired
rank-four blocks. The wedge norm bound in each block gives
\[
 \ell\ge2-(1-e'_x)(2-e'_M)-e'_x e'_M
     =2e'_x+e'_M-2e'_x e'_M.
\]
Here \(e'_x<1/20\) and \(\tau<3/20\). Therefore
\(\kappa\ge(153/100)(2e'_x+e'_M)\).
Apply the fixed five-form estimate to each of the two pairs, using its
actual five remaining legs as \(Y\). Their summed reference leakage
is \(2e'_x+e'_M\). This gives
\[
 (L_{01}+L_{02}-4)_+\le (2200/153)\kappa<16\kappa
 \quad\text{if }0<\kappa<1/32.
\]
The same reasoning bounds each individual positive excess by
\((2200/153)\kappa\). For \(\kappa\ge1/32\) the universal
joint bound \(L_{01}+L_{02}-4\le1/2\) and the individual
\(L_{ij}\le7/3\) give both asserted bounds. At zero defect the
Fourier rounding has zero leakage.

## From the geometric bound to spectral optimality

The [joint mixed estimate](rank7_three_level_124_conditional_matching.md)
and the exact scalar comparison now control every single-unitary frame.
For a fixed spectrum with possibly positive exterior-overlap gain, the
verified scalar inequality is strict at that spectrum. It permits
retaining a fixed positive fraction of the actual defects in the
purity comparison. To see this, on the positive-gain branch the
parameter \(a\) of the scalar comparison lies in \([0,2]\).
The full comparison has a strictly positive minimum over that interval
for the fixed spectrum, by its positive derivative and strict bound
at \(a=0\). A sufficiently small uniform scaling down of the
payment coefficients therefore leaves a positive comparison. The
absorption of the compression trace correction also survives that
scaling. The no-gain branch retains the entire defect.
The [open-neighborhood transfer](rank7_open_interior_neighborhood.md)
and the paired Cauchy–Schwarz and stabilizer padding reductions
give the full statement.

[Sierant, Theorem 17 and Eq. (147)](https://arxiv.org/html/2609.13106v2)
