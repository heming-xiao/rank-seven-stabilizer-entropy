# Rank-seven fifth probability, head gaps and tight Pauli constraints

November 18, 2026. The ordered positive Schmidt probabilities are
\((\alpha,\beta,\gamma,a,b,c,d)\). The optimality results below
cover order-two nonlocal stabilizer Rényi entropy over arbitrary
complex local unitaries on every qubit bipartition.

## Global optimality in two additional spectral regions

Every spectrum with \(b\ge3d\) has the sorted computational
representative as a global optimizer, allowing the other
five ordered coordinates to vary. This replaces the previous
\(b\ge9d\) sufficient threshold. The same comparison also
settles the region
\[
 (q\le b/2\ \text{or}\ h\le3b/2),\qquad
 bc(h+4k+3q)\ge22d^3,
 \qquad (h,k,q)=(\alpha-\beta,\beta-\gamma,\gamma-a).
\]
The proof preserves a strict paired margin, including the boundary
of each criterion, so the local Clifford optimizer classification
and the open spectral neighborhood transfer apply.

When \(H=hq-b(h+3q)-5b^2/2\le0\), a convex combination of the
same-frame split and the full-spectrum singleton price cancels
the shared trace excess. Only one actual mixed square and its
distinct anticommuting terms are then required. For \(H>0\), the
existing tied-middle payment and a strict quadratic bound control
the two excesses separately. The exact example below \(b=3d\)
has zero width in both standard compression cuts. Its pure
exterior relaxation satisfies 119 constraints and gives positive
gain \(752983/7680000\), while the physical comparison is strict.
[Proof and example](rank7_large_fifth_probability.md) ·
[Independent review](reviews/rank7_large_fifth_probability_independent_review.md) ·
[Exact verifier](../verification/verify_rank7_large_fifth_probability.py).

## Dimension-independent cubic Pauli bound tight at the reference

Let \(v_i=L_{0i}-2\), \(i=1,2\). The physical subgroup argument
gives \(2\cdot10^{14}E_f\ge\max(0,v_1,v_2)^3\) in every local
qubit dimension. Each positive edge suffices to force a large
Pauli coset with a genuinely odd majority. Averaging its approximate
invariant plane constructs an exact rank-two invariant projection,
and the radical block estimates force a contradiction if the
measured flag error is too small.

The only tail Pfaffian needed by the pointwise argument is
bounded using \(w_{0345}+w_{0346}\). Replacing the larger
four-term tail sum by this pair yields the affine error
\(E_f^{\rm tight}\), zero at the sorted computational reference.
The cubic comparison and the two linear Pauli Gram bounds
hold with this tighter error and the same constants. The
three choices of anchor among the leading labels give
simultaneous constraints. The cubic bounds extend to the
closed convex hull in arbitrary dimension, and their rational
tangents give linear constraints. They exclude the entire open
segment from the computational reference to any point on the
old saturated face. For the linear Pauli Gram bounds, both
sides vanish at the sorted reference.

The original direct whole-face argument gives a strict affine
margin \(10^{-130}\). The cubic theorem gives the stronger
three-term bound
\[
 D_{57}+(1/2-\nu)+(2d_1-\nu)>1.9\cdot10^{-17}
\]
also on the closed convex hull. Those three terms alone exclude
the corresponding larger face. The applicability of the cubic
cut near the reference comes from tightening the tail term.
For the original flag the error remains at least one even
after rotating the basis within the seven-dimensional reference
support. A cubic cut by itself has zero first derivative in
the excess at the reference. The tight linear Gram constraints
are available for the remaining first-order comparison.
[Cubic theorem](rank7_physical_flag_cubic_cut.md) ·
[Reference-tight refinement](rank7_reference_tight_flag.md) ·
[Independent review](reviews/rank7_physical_flag_cubic_cut_independent_review.md) ·
[Application to packing variables](rank7_physical_cut_interface.md) ·
[Pauli constant checks](../verification/verify_rank7_saturated_face_separation.py) ·
[Reference incidence checks](../verification/verify_rank7_physical_cut_interface.py).

## A neighborhood of every Fano table

Three nearly saturated Fano four-wedges already force the frame
near a common affine eight-point stabilizer code, by simultaneous
rounding of three rank-four codes. The earlier low-leakage theorem
then gives nonpositive exterior gain. At a positive physical gain,
each of the 840 distinct relevant three-face deficits exceeds
\(\min\{(4\cdot10^9)^{-1},(d/\alpha)^3/250880\}\), including every
relabeling. This lower bound is at least \(1/(250880\cdot231^3)\)
in the remaining spectrum domain. The weak form applies to the
closed convex hull of the positive-gain frames.
[Proof](rank7_fano_table_physical_collar.md) ·
[Independent seven-plane audit](reviews/rank7_fano_table_physical_collar_independent_review.md) ·
[Incidence and threshold checks](../verification/verify_rank7_physical_cut_interface.py).

## Checkpoint and remaining comparisons

The live C++ exact interval certificate for \(b=c\) has accepted
48,300,000 leaves at observed depth 55. Its pending stack remains
nonempty. The full \(b=c\) spectrum family remains a candidate.
[Compiled verifier](../verification/verify_rank7_equal_fifth_sixth.cpp) ·
[Candidate proof](rank7_equal_fifth_sixth_candidate.md).

All remaining spectra satisfy \(a-b<5d/7\),
\(101/100<c/d<9/5\), \(b/d<3\), \(\alpha/d<231\),
\(96d(\beta-\gamma)>bc\), and \(5g>bL\). They also lie outside
the new head-gap region above. A potentially violating paired
frame has both leading excesses positive and must meet the
existing two-sided ratio restriction. For \(H<0\) use the
additional negative-shared bound from (7) of the new
fifth-probability proof. The tight Pauli Gram constraints can
be combined with the mixed comparison and the independently
allocated full nominal compression widths on their stated
domains. The unrestricted scalar comparison in this remaining
region and arbitrary fourth/fifth ties are open.
[Previous ratio bound](rank7_excess_ratio.md) ·
[Nominal widths](rank7_full_nominal_widths.md).

The targeted literature check revisited Sierant's rank-seven
compression theorem and rank-six matching theorem, which form
the input for these extensions. Franchini and Giampaolo's
general Schmidt-gauge statement proves exact local-unitary
optimization on qubit-versus-rest cuts. Viscardi, Leone and
Hamma's November revision solves the optimization for
log-stabilizer fidelity, a different objective from order-two
stabilizer Rényi entropy. The papers examined do not establish
these two rank-seven spectral criteria or the tight flag theorem.
Public priority remains unconfirmed.
[Sierant, Sections V.4 and C.11](https://arxiv.org/html/2609.13106v2#A3.SS11) ·
[Franchini and Giampaolo](https://arxiv.org/abs/2608.02745) ·
[Viscardi, Leone and Hamma](https://arxiv.org/abs/2609.04119v2).

