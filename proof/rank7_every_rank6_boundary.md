# Every rank-six spectrum has a rank-seven neighborhood of optimality

November 17, 2026. For each \(s\in(0,1]\) there is an explicit positive cutoff \(r_6(s)\), independent of the qubit dimensions, such that an ordered rank-seven spectrum with
\[
  t_0=1,\qquad t_5\ge s,\qquad 0<t_6\le r_6(s)
\]
satisfies global computational-basis optimality at order two. All multiplicity patterns are allowed. Hence every fixed rank-six Schmidt spectrum lies at the boundary of a full relative neighborhood of rank-seven spectra with the same global optimality. The proof breaks no degeneracy and needs no gap among the first six probabilities.

## Round the six-dimensional support

Use parameter \(g=s/2\), rank bound \(R=7\), and the fixed extraction constants \(\eta_*\) and \(\mathcal A\) of the [high Pauli coset truncation](rank7_generic_rank6_neighborhood.md) in its [unified formulation](rank7_boundary_proof.tex). For \(\eta=\Delta_d(C)/d<\eta_*\), it gives \(G,C_{\rm hi},D=\mathcal E_G C\) with
\[
 \|C-C_{\rm hi}\|_{\rm op}<5g/16,\qquad
 \|D-C_{\rm hi}\|_{\rm op}\le g/16,\qquad
 \|C-D\|_{\rm HS}^2\le\mathcal A\eta.
\]
Require \(t_6\le s/2\), so the sixth-to-seventh gap is at least \(g\). At the midpoint between these eigenvalues, \(C_{\rm hi}\) has exactly six eigenvalues above the cutoff. It is scalar on the common character blocks of \(G\), whose dimensions are a common power of two dividing six, hence one or two. The same upper subspace \(Q\) belongs to \(D\), since the two matrices preserve these blocks and their difference is at most \(g/16\), below the cutoff margin \(3g/16\).

Let \(P\) be the actual leading six-space. The spectral residual inequality from the [six-space rotation proof](rank7_uniform_leading_doublet_boundary.md) gives
\[
 \operatorname{tr}P(I-Q)\le4\mathcal A\eta/g^2,
 \qquad \|K\|_{\rm op}^2\le20\mathcal A\eta/g^2 .
\]
Here \(e^K\) is the direct principal-angle rotation taking \(Q\) to \(P\), with \(K\) skew-Hermitian and off-diagonal relative to \(Q\oplus Q^\perp\). Pulling the actual Schmidt frame back by \(e^{-K}\) gives a reference \(C_{\rm ref}\) with the first six eigenvectors in \(Q\), the seventh orthogonal, and identical probabilities.

## Geometry of the coordinate six-space

After a Clifford, \(Q\) consists of six computational labels. If the group blocks have size two, these labels are three two-point cosets of a common direction. Their images in the quotient span an affine plane, whose preimage is an affine eight-point space \(H\) containing \(Q\). If \(G\) is maximal, there are two possibilities according to the six labels of \(Q\).

If \(Q\) is contained in an eight-point affine space \(H\), the two missing labels form a coset of the direction \(a\) given by their difference. Thus in every case with \(Q\subset H\), the six labels are the other three cosets of that direction. The [stationarity computation](rank7_uniform_leading_doublet_boundary.md) depends only on this arrangement and on \(K\) being off-diagonal between \(Q\) and \(Q^\perp\). Specifically, all-head wedges use directions containing \(a\) and their first variations use disjoint directions. Wedges containing the tail use directions inside \(H\) avoiding \(a\), and their first variations again use disjoint directions. At the reference the pairs \(01,02\) lie in \(H\), so the [affine-eight fixed-pair bound](reviews/rank7_two_link_independent_review.md) gives \(L_{01},L_{02}\le2\). Taylor then gives
\[
 (L_{0i}-2)_+\le320\|K\|^2\le6400\mathcal A\eta/g^2
 \quad (i=1,2).
\]
With the two forward coefficients each at most \(2t_6\), their bracket is bounded by \(25600t_6\mathcal A\eta/g^2\). Multiplication by \(168\) and subtraction of \(\eta\) proves optimality on this branch if \(t_6\le g^2/(4300800\mathcal A)\).

If the six labels are not contained in an affine eight-point space, they contain at most one affine plane. Indeed, two distinct affine planes contained in six points must meet in two points. They then share an affine line, so their union lies in an affine three-space; since their union already has six elements it would be all of \(Q\). The stabilizer projector \(\Pi_{\rm F}\) compressed to \(\Lambda^4 Q\) is therefore zero or \(q\) times a coordinate rank-one projector, where \(q=4/d\). Consequently
\[
 q^{-1}c_{\rm F}(C_{\rm ref})\le t_0t_1t_2t_3+20t_6 .
\]
The first term bounds the operator norm of the leading-four part. For the tail part there are \(\binom63=20\) wedges, each with coefficient at most \(t_6\) and normalized squared overlap at most one by the one-hole inequality. On the sorted reference the three planes \(0123\), \(0145\), and \(2345\) contribute, so
\[
 q^{-1}c_{\rm F}(C_{\rm CB})\ge t_0t_1t_2t_3+2s^4 .
\]
Along the rotation of the complete frame each normalized squared wedge overlap changes at speed at most \(8\|K\|\), again by the one-hole inequality. The sum defining \(c_{\rm F}/q\) has 35 terms with weights at most one, so
\[
 q^{-1}|c_{\rm F}(C)-c_{\rm F}(C_{\rm ref})|\le280\|K\|.
\]
If \(20t_6\le s^4/2\) and \(280\|K\|\le s^4/2\), the exterior overlap of \(C\) is strictly less than the sorted value. In rank seven the existing compression \(Q_{(1^4)}\le q c_{\rm F}\) therefore gives strict purity comparison.

## Parameter choice and unrestricted comparison

Set
\[
 \eta_0=\min\{\eta_*,\ g^2s^8/(20\cdot560^2\mathcal A)\},\qquad
 r_6(s)=\min\{s/2,\ s^4/40,\ \eta_0/336,\ g^2/(4300800\mathcal A)\}.
\]
If \(\eta<\eta_0\), the two branches above apply. For \(\eta\ge\eta_0\), the universal \(L_{ij}\le5/2\) and \(\gamma_{01}\le2t_6\) bound the forward purity excess by \(336t_6-\eta\le0\). This proves every paired comparison. Cauchy–Schwarz combines the physical marginals, and padding the smaller side with computational stabilizer ancillas gives arbitrary bipartitions. When the cutoff is strict, every paired maximizer has zero Pauli defect. Thus the physical marginals have commuting Pauli supports. For distinct positive probabilities the exact equality states are local Clifford images of the sorted representative. [Forward coefficient and normalization](rank7_forward_coefficients_independent.md) · [Paired comparison, compression and defect](https://arxiv.org/html/2609.13106v2)

For a fixed rank-six spectrum, its sixth positive probability gives a positive limiting \(s\) in the normalization \(t_0=1\). A sufficiently small relative rank-seven neighborhood therefore meets the cutoff on the new seventh probability.
