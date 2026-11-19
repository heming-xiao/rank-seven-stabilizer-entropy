# Rank-seven neighborhoods across a split leading doublet

November 17, 2026. Let \(t_0=1\ge t_1\ge\cdots\ge t_6>0\) be the ordered Schmidt probabilities at rank seven after a common rescaling, and set \(b_i=t_i-t_{i+1}\), with \(t_7=0\). Fix \(g>0\). Suppose \(b_1\ge g\) and at least one even-index gap \(b_j\) with \(j\in\{0,2,4,6\}\) is at least \(g\). Then there is a dimension-independent explicit \(\varepsilon_{\rm odd}(g)>0\) such that \(t_6\le\varepsilon_{\rm odd}(g)\) gives sorted computational-basis optimality over all local unitaries. The first gap \(b_0\) can go to zero. In particular, this supplies a full rank-seven neighborhood of each fixed rank-six spectrum with an isolated highest doublet and any lower cluster of odd multiplicity.

## Maximal Pauli rounding from an odd spectral count

Apply the [Pauli extraction and high logical truncation](rank7_generic_rank6_neighborhood.md) to the paired marginal probability matrix \(C\), using \(R=7\), parameter \(g\), and the constants \(\eta_*, \mathcal A\) in that proof. The proof up to forming the lifted commuting group \(G\) and high-coset truncation \(C_{\rm hi}\) is independent of the first spectral gap. In the notation of the [unified manuscript](rank7_boundary_proof.tex), for \(\eta=\Delta_d(C)/d<\eta_*\) it gives
\[
 \|C-C_{\rm hi}\|_{\rm op}<5g/16,\qquad
 \|C-\mathcal E_GC\|_{\rm HS}^2\le\mathcal A\eta .
\]
The truncation keeps only logical cosets whose mass exceeds the fixed logical threshold, so \(C_{\rm hi}\) is scalar on the simultaneous character spaces of \(G\). The bound for \(\mathcal E_G\) uses the labels outside \(G^\perp\) and does not require maximality.

Let \(j\) be even with \(b_j\ge g\) and take the cutoff \((t_j+t_{j+1})/2\). The perturbation bound and Weyl's inequality show that \(C_{\rm hi}\) has exactly \(j+1\) eigenvalues above the cutoff, counted with multiplicity. This number is odd. Every \(G\) character block has the same dimension, a power of two, which must divide \(j+1\). Hence the dimension is one and \(G\) is maximal. The even-index condition expresses existence of an isolated odd-dimensional upper spectral subspace. In particular, an isolated cluster of odd dimension forces an odd count at at least one of its delimiting cuts.

## Pay the exact forward coefficients

Let \(P\) be the leading two-dimensional spectral projection of \(C\). Its gap to the complement is at least \(g\), even if the two leading eigenvalues coincide. The entrywise spectral commutator comparison and Pauli averaging give
\[
 \|P-\mathcal E_G P\|_{\rm HS}^2\le\mathcal A\eta/g^2.
\]
Let \(Q\) span the two largest coordinate masses of \(P\) in the stabilizer basis of \(G\). These masses sum to at least the sum of their squares over all coordinates, since the full diagonal is a positive contraction with trace two. Thus \(1-\operatorname{tr}(PQ)/2\le\mathcal A\eta/(2g^2)\). The two-anchor code estimate gives
\[
 (L_{01}-2)_+\le 5\mathcal A\eta/g^2.
\]

For the second term, the forward coefficient \(\gamma_{02}=b_0b_2t_5t_6\) vanishes when either \(b_0\) or \(b_2\) is zero. If both are positive, the first and third eigenlines are simple, with gaps at least \(b_0\) and \(h=\min(g,b_2)\), respectively. Their squared dephasing losses are bounded by \(d_0=\mathcal A\eta/b_0^2\) and \(d_2=\mathcal A\eta/h^2\). Choose two distinct stabilizer references with squared infidelities at most \(2d_0,2d_2\). If both bounds on the dephasing loss are below \(1/2\), the two largest-mass coordinates are distinct by orthogonality. If one or both bounds are at least \(1/2\), assign each such line any remaining coordinate, using \(1\le2d_i\). The [asymmetric anchor bound](rank7_simple_top_boundary.md) gives
\[
 \gamma_{02}(L_{02}-2)
 \le b_0b_2 t_6\cdot29\sqrt{(2d_0)(2d_2)}
 \le 58\,t_6\mathcal A\eta/g
\]
because \(t_5\le1\) and \(b_2/h\le1/g\). This estimate stays uniform as the first gap closes.

Since \(\gamma_{01}\le2t_6\) and \(g\le1\), the full bracket
\(\gamma_{01}(L_{01}-2)+\gamma_{02}(L_{02}-2)\)
is at most \(68t_6\mathcal A\eta/g^2\) for \(\eta<\eta_*\).
For \(\eta\ge\eta_*\), the universal \(L_{ij}\le5/2\) instead bounds the bracket by \(2t_6\).
The [forward-gap purity comparison](rank7_forward_coefficients_independent.md) multiplies that bracket by \(168\) and subtracts at least \(\eta\). Thus one may take
\[
 \varepsilon_{\rm odd}(g)=\min\{\eta_*/336,\;g^2/(11424\mathcal A)\}.
\]
As usual the geometric-mean comparison and stabilizer padding give arbitrary physical cuts. At strict cutoff both paired defects must vanish at an optimizer; for distinct nonzero probabilities the optimizers are precisely the local Clifford images by the one-sided equality theorem. [Paired reduction and Pauli defect](https://arxiv.org/html/2609.13106v2)

At a fixed rank-six boundary with an isolated leading doublet and a lower cluster of odd multiplicity, choose \(g\) strictly below the corresponding positive separation distances. Fully split perturbations preserve the relevant gaps and can have \(t_6\) arbitrarily small. This proves the full relative neighborhood, including changes to the leading two-fold degeneracy. In particular it covers limiting multiplicities \((2,1,1,1,1)\), \((2,2,1,1)\) in any order below the doublet, and \((2,3,1)\) or \((2,1,3)\). The all-even patterns \((2,2,2)\) and \((2,4)\) require another argument.
