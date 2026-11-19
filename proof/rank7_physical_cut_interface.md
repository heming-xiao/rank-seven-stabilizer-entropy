# Applying the rank-seven physical flag cut to the packing variables

November 18, 2026. Let \(v_1=L_{01}-2,\ v_2=L_{02}-2,\ \nu=v_1+v_2\),
\(u=1-2\nu-x\), and \(m_0=2d_1-\nu\). These are the same unweighted
frame quantities used in the paired reduction. Let \(C=2\cdot10^{14}\).
The physical flag theorem and its linear interface give
\[
 J=3(D_{57}-x)+2u+m_0\ \ge\ E_f
       \ \ge\ C^{-1}\max(0,v_1,v_2)^3.                         \tag{1}
\]
The three terms of \(J\) are nonnegative. The right side is continuous
and convex in the two signed excesses, so (1) holds throughout the
closed convex hull of physical frames, allowing arbitrary dimensions.
This comparison is a feasibility constraint on the exterior variables.
The mixed or anticommuting payments in the objective remain available
when applying it.
[Flag theorem](rank7_physical_flag_cubic_cut.md) ·
[Linear interface, Eq. (5)](rank7_saturated_face_exclusion_and_stability.md).

## A three-row affine separation

Put \(B=D_{57}+(1/2-\nu)+m_0\). All three summands are nonnegative
and \(J\le4B\). Thus \(4CB\ge[(1/2-B)_+/2]^3\). In particular
\[
                           B>19\cdot10^{-18}.                  \tag{2}
\]
Indeed \(B\le19\cdot10^{-18}\) would give
\(4CB\le 19/1250\), while \(1/4-B/2>249/1000\) and
\((249/1000)^3>19/1250\). This excludes the larger face defined by
\(D_{57}=0,\ \nu=1/2,\ 2d_1=\nu\). It also gives the same lower
bound on the full six-term face functional. The estimate applies to
the closed convex hull, as it follows directly from (1).

## Linear constraints and the interval for violating frames

At any rational \(t\in[0,1/3]\), add both affine constraints
\[
                     CJ\ge 3t^2v_i-2t^3,\qquad i=1,2 .
\]
Their intersection over all such tangency points recovers (1).
For a fixed spectrum with \(F>0\) and \(g>0\), a violating frame has
\(\nu>0\) and \(\ell/F<v_1/\nu<10g/(bL)\). It therefore satisfies
\[
 CJ\ \ge\ r_*^{\,3}\nu^3,\qquad
 r_*=\max\left\{\tfrac12,\frac{\ell}{F},1-\frac{10g}{bL}\right\}.
\]
This follows from \(v_2=\nu-v_1\). It permits a single scalar
constraint in the excess variables when an interval proof retains
only \(\nu\). [Ratio bounds](rank7_excess_ratio.md).

## Behaviour at the computational reference

The seven coordinate planes include \(0123\) and \(0356\). The
reference has \(A_0'=T_Q=C_Q=C_*=0,\ T_Y=1\), hence \(E_f=1\)
and \(v_1=v_2=0\). The cubic inequality is strict there. If the old
convex packing relaxation contains a point with positive linear
exterior gain, points on the segment from the reference to that
point have positive gain arbitrarily close to the reference.
Continuity gives a small initial segment on which the cubic
cut holds. Thus this cut can exclude a saturated face or constrain
the amplitude of a putative gain. The sign of a positive linear
packing direction through the reference still requires a tight
physical comparison or a contribution from the paired defect.


## Tight flag errors and the three possible anchors

The narrower Pfaffian term
\(T_* = w_{0345}+w_{0346}\) may replace \(T_Y\) in the flag proof.
Write
\[
 E_f^{\mathrm{tight}}=A_0'+T_Q+T_*+C_Q+C_* .
\]
This affine functional is nonnegative and zero at the sorted
computational reference. It satisfies the same cubic cut (1) with
\(E_f^{\mathrm{tight}}\) in place of \(E_f\). The two linear
Pauli Gram comparisons in the face note also survive with the
narrower error. Their Gram terms vanish at the reference, so these
are tight affine constraints in the joint exterior and Pauli
Gram variables.
[Pfaffian refinement](rank7_reference_tight_flag.md) ·
[Independent review](reviews/rank7_physical_flag_cubic_cut_independent_review.md).

For each choice of anchor among the three highest labels, permute
the leading triple accordingly and extend it to the affine
permutation of the binary three-space fixing the missing point 7.
The extension exists because the three leading points and 7 are an
affine basis. It fixes their completion 3 and preserves the
seven reference planes. Thus there are three affine errors
\(E_j\), each tight at the same reference, satisfying
\[
 C E_j\ge \max\{0,L_{ji}-2:i\in\{0,1,2\}\setminus\{j\}\}^{3},
 \qquad j=0,1,2.
\]
They hold simultaneously on a single physical frame and on the
closed convex hull of physical frames. If \(M\ge m\ge s\) are the three
nonnegative leading-edge excesses in decreasing order, then
\(C\sum_j E_j\ge2M^3+m^3\). This follows because the edge of
size \(M\) is incident to two vertices and the third is incident to
the edge of size \(m\). Use the individual tangent inequalities
when retaining these errors in a linear program.

On the old saturated face, \(E_f^{\mathrm{tight}}=0\) because
\(0\le E_f^{\mathrm{tight}}\le E_f\le J=0\). Its entire
open segment toward the reference has \(E_f^{\mathrm{tight}}=0\)
and \(\nu>0\) by affinity. The cubic cut forbids that segment
from the closed physical convex hull, even arbitrarily close to
the reference. The tight linear Gram rows provide a further
comparison on directions with a positive exterior error.
[Exact incidence and rational checks](../verification/verify_rank7_physical_cut_interface.py).


## Reference weight collar

For a compressed four-dimensional skew matrix, the three-plane's
internal squared mass is the full \(u+v\) minus a squared column
norm in \([v,u]\). Thus \(r\in[v,u]\), and
\(r(1-r)\le u(1-v)\le u+v-2uv\). The normalized Pfaffian and pair
identities give the asserted \(6(1-w_I)\) upper bound on the
triangle defect. The code rounding is valid below its small
threshold. Exactly one out-of-code leg contributes zero by
affine XOR. The bound for two or three out-of-code legs among
the first three may keep the fourth unit vector whole, so all
terms are covered once. The Young inequality
\(\sqrt{3ae}\le e/4+3a\) gives the stated fourth-leg bound
\(e\le212(1-w_I)\).

Any two of the codes share at least one incident near-code
vector. The expectations of two proposed stabilizer generators
are each at least \(1-424/(4\cdot10^9)\) on that vector.
Their squared sum exceeds one, which forces commutation.
The distinct membership patterns give disjoint, nonempty
cells. Four such cells inside each rank-four code force each
positive-incidence cell to be a single common-basis point.
Planes \(0123,0145,0246\) show that those seven points are
in the affine span of \(0,1,2,4\), and seven distinct points
force this span to have dimension three. The stronger total
leakage comparison uses the full trace \(4\) of each code
to bound the entire sum over nonincident legs, so the total
over the seven cells is at most twice the sum of the incident
leakages. The resulting \(448 B_{\mathcal F'}\) is at most
\(s^3/560\) under (2), in the normalization required by the
existing exterior theorem. These rows are necessary for
positive physical gains. Their closed convex consequence is
for the closure of the convex hull of the gain-positive frames.
[Reference collar](rank7_fano_table_physical_collar.md) ·
[Existing low-leakage result](rank7_low_defect_interior.md).

