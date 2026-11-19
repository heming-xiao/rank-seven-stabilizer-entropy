# Joint mixed-sector estimate for the rank-seven 1+2+4 spectrum

November 17, 2026. Consider rank-seven Schmidt probabilities proportional to
\((1,r,r,s,s,s,s)\), \(1\ge r\ge s>0\). Work with the single-unitary
objective \(G\). Let \(P_0\) project onto the highest line, \(P_3\) onto
the three leading lines, and \(E_H\) onto their two wedges consisting of
the highest line and one of the middle lines. Write \(\mathcal B\) for the
bad-phase orthogonal projection from the [mixed-sector identity](rank7_two_level_defect_transport.md).
Define \(u=\mathcal B E_H\), \(\kappa=2\|u\|^2\), and the geometric
excess \(\nu=L_{01}+L_{02}-4\). Let \(A\) be the normalized exterior
occupancy of the wedges containing all three leading lines, so
\(x=1-A\ge0\) by the one-hole bound.

## Three conditional matching weights

For each skew Pauli coordinate, let \(p=p_{01}+p_{02}\), \(m=p_{12}\).
Here \(p_{ij}\) is the modulus squared of the corresponding skew-unitary
matrix entry in an orthonormal eigenframe. Write \(\langle\cdot\rangle\)
for \(2/d\) times the sum over skew labels. Then \(\langle p\rangle=2\),
\(0\le p+m\le1\), and
\(\kappa=\langle p(1-p)\rangle\). The last identity uses the fact that the
wedge product of any two vectors in the image of \(E_H\) vanishes.

The squared entries on the seven positive labels form a convex
combination of matchings. Row sums are at most one and the odd-set
conditions follow because any odd-sized skew compression has even rank
and operator norm at most one. Edmonds' matching-polytope theorem now
applies. A matching with a highest–middle edge has maximal weighted
sum \(M_1=r+rs+s^2\). With a middle–middle edge this sum is
\(M_0=r^2+s+s^2\). If no edge connects any of the highest three labels
it is \(M_{\varnothing}=s+2rs\). For this last claim, any unmatched
leading label can be connected to a spare tail, or replace one endpoint
of an existing tail–tail edge, without decreasing the objective. Matching
all three to distinct tails gives the stated value. Consequently,
for \(g=(1-r)(r-s)\) and the weighted sum \(s_C=\sum_{i<j}t_i t_j p_{ij}\),
\[
 s_C\le M_1-g(1-p)-(r-s)^2(1-p-m).
\]

Write \(B\) for the normalized exterior occupancy with the highest line,
one middle line and two tails. Then \(\nu=2A+B-4\), and polarization
gives
\[
 2\langle u,L_-(C)\rangle=2r+2rsA+s^2B-\langle p\,s_C\rangle.
\]
Each leading pair contributes its weighted disjoint remaining pair
in this formula. A wedge with all three highest legs and a tail is
counted twice with weight \(rs\). The other wedges counted have one
leading pair and tail weight \(s^2\). The reference sum is
\(2r+2rs+2s^2=2M_1\). Substitution gives the joint estimate
\[
 2\langle u,L_-(C)\rangle\ge
 g\kappa+s^2\nu-2s(r-s)x+
 (r-s)^2\langle p(1-p-m)\rangle .
\]
The last term is nonnegative. The estimate uses a single shared
projector and is invariant under a basis change within the middle
eigenspace.

## A separate anticommuting contribution

On the second exterior power,
\(E_H=(P_0\otimes P_3+P_3\otimes P_0)|_{\Lambda^2}\).
Polarizing the Pauli identity for \(L_-(C)=\mathcal B\Lambda^2 C\),
each full ordered tensor term is projected onto pairs of anticommuting
Pauli labels. Its squared Hilbert–Schmidt norm is \(J(P_0,P_3)\) or
\(J(P_3,P_0)=J(P_0,P_3)\). Restricting the sum to the exterior subspace
and using the triangle inequality gives \(\kappa\le8J(P_0,P_3)\).

For each Pauli \(W\), the eigenvalue differences across the two nested
spectral cuts give
\[
 \|[C,W]\|_{\rm HS}^2
 \ge (1-r)^2\|[P_0,W]\|_{\rm HS}^2+
          (r-s)^2\|[P_3,W]\|_{\rm HS}^2 .
\]
If a matrix element crosses both cuts, the actual gap is at least the
sum of the two individual gaps, whose square covers both listed terms.
Apply the commutator representation of \(J\) in each slot in turn.
This gives \(J(C,C)\ge 2g^2J(P_0,P_3)\), and hence the additional
payment \(2J(C,C)\ge(g^2/2)\kappa\).

The same argument holds for arbitrary ordered rank-seven probabilities.
Replace \(1-r\) by \(t_0-t_1\) and \(r-s\) by \(t_2-t_3\). This version
does not use ties or a choice of basis in the middle two-dimensional
space.

## Consequence for arbitrary seven probabilities

The [uniform shared-anchor estimate](rank7_124_small_defect_closure.md)
bounds both \(\nu_+\) and each individual positive excess by
\(16\kappa\), independently of the spectrum.
For any ordered positive rank-seven spectrum, let
\[
 \gamma_{02}=(t_0-t_1)(t_2-t_3)t_5t_6,\qquad
 \gamma_{01}=\gamma_{02}+t_6^2(t_1-t_2)(t_0-t_3).
\]
The [forward gap comparison](rank7_forward_coefficients_independent.md)
bounds the normalized exterior gain by
\(\gamma_{01}(L_{01}-2)+\gamma_{02}(L_{02}-2)\).
Write this as \(\gamma_{02}\nu+(\gamma_{01}-\gamma_{02})(L_{01}-2)\).
Combining the geometric bounds and the separate
anticommuting contribution proves unrestricted computational-basis
optimality on every cut whenever
\[
 (t_0-t_1)^2(t_2-t_3)^2 \ \ge\ 5376\gamma_{01}.
\]
Indeed the exterior gain is at most
\(16\gamma_{01}\kappa\), which is multiplied by 168 in the purity
comparison, and the anticommuting term alone pays
\((t_0-t_1)^2(t_2-t_3)^2\kappa/2\).
The inequality has no degeneracy requirement on the seven
probabilities. It is a sufficient region and leaves spectra for
which the two leading gaps are small relative to the tail weights.

## A sufficient spectral condition without a rounding estimate

Use the [block packing and compression estimates](rank7_three_level_124_packing_and_scalar.md).
They give \(\nu\le1/2\) when positive and, with
\[
 H=r(1-r)-(2+r)s+s^2/2,\qquad
 \lambda=(1-s)(r-s)/2,\qquad a=2(r-s)x/(s\nu),
\]
bound the purity gain by \(168s^2(H-\lambda a)\nu\), before subtracting
the actual mixed and compression defects. The two compression gaps
give at least \(48s^2h\nu\) after absorption of a trace correction
by its packing loss, where
\[
 h=(\sqrt r-\max(r,\sqrt s))^2+(\sqrt s-r)_+^2 .
\]
For \(a<1\), the joint estimate and Cauchy–Schwarz give mixed payment
at least \(48g s^2(1-a)\nu\) by the arithmetic–geometric mean. When
\(a\ge1\), use nonnegativity of the actual mixed payment. This yields
\[
 G-G_{\rm CB}\le s^2\nu[168H-168\lambda a-48h-48g(1-a)_+] .
\]
The right-hand bracket is nonincreasing in \(a\), since
\(168\lambda\ge84g>48g\) when \(g>0\). The cases with no positive gain
are already covered. Thus the following closed spectral region is
sufficient on every bipartition:
\[
 (12+9r)s-\tfrac72s^2+2h\ge5r(1-r).
\]
Strict inequality retains a fixed positive fraction of the actual
defects at each spectrum and yields a full rank-seven open neighborhood
by the [strict-margin transfer](rank7_open_interior_neighborhood.md).
For instance, \((r,s)=(1/2,1/10)\) satisfies the strict condition.

## Complete three-level comparison

The exact scalar comparison in the block-packing note proves optimality
whenever \(\nu\le16\kappa\). The uniform geometric bound establishes this
condition for every frame, completing the \(1+2+4\) family without a
spectral restriction. Its strict defect reserve gives full relative
open neighborhoods in the rank-seven simplex.

[Sierant, Proposition 2 and Theorem 7](https://arxiv.org/html/2609.13106v2) · [Edmonds, matching polytope theorem](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn1-2p125_A1b.pdf)
