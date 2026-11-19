# Rank-seven neighborhoods with only the top spectral gap

November 17, 2026. For every \(g>0\), there is an explicit positive cutoff independent of the dimensions such that rank-seven probabilities with \(t_0=1\), \(t_0-t_1\ge g\), and \(t_6\) below the cutoff have sorted computational-basis optimality over all local unitaries. No other spectral gap is required. In particular every fixed rank-six spectrum with a simple largest probability has a full rank-seven neighborhood of optimality.

Use the [Pauli extraction and maximal-group refinement](rank7_generic_rank6_neighborhood.md) with \(R=7\), using \(g\) for just the first gap. The refinement only needs the largest eigenvalue to be simple. For \(\eta=\Delta_d(C)/d<\eta_*\), it yields a maximal Pauli group \(G\) with \(\|C-\mathcal E_G C\|_{\rm HS}^2\le\mathcal A\eta\). The leading line \(x_0\) has squared infidelity \(e_0\le\mathcal A\eta/g^2<1/4\) from some stabilizer basis vector \(v_0\).

## An asymmetric anchor estimate

For an orthonormal pair \(x,y\) and two distinct members \(v,w\) of one stabilizer basis, write \(e_x=1-|\langle v,x\rangle|^2\), \(e_y=1-|\langle w,y\rangle|^2\). For any five-dimensional orthogonal tail, the normalized five-set occupancy satisfies
\[
 (L_{xy}-2)_+\le29\sqrt{e_xe_y}.
 \tag{1}
\]
Indeed, the operator \(L=2I-M_Y\) satisfies \(-I/2\preceq L\preceq2I\), and both compressions to \(v\wedge\mathcal H\) and \(w\wedge\mathcal H\) are nonnegative. Decompose the unit wedge as \(c(v\wedge w)+\eta_v+\eta_w+z\), with the middle two components containing one respective reference vector and the last entirely outside their plane. If the first three self-expectations are \(a^2,b_v^2,b_w^2\), the first two relevant cross terms are bounded by the star Cauchy–Schwarz inequalities:
\[
 a^2+b_v^2+b_w^2-2a(b_v+b_w)\ge-2b_vb_w\ge-4\|\eta_v\|\|\eta_w\|.
\]
The centered norm \(\|L-3I/4\|\le5/4\) costs at most another \((5/2)\|\eta_v\|\|\eta_w\|\) and at most \((5/2)\|z\|\) for its cross term with the other components together. Its own contribution is at least \(-\|z\|^2/2\). Direct wedge expansion gives \(\|\eta_v\|\le2\sqrt{e_y}\), \(\|\eta_w\|\le2\sqrt{e_x}\), and \(\|z\|\le\sqrt{e_xe_y}\). Adding these losses gives (1). [Original code estimate](rank7_large_top_pair_gap.md)

## The forward coefficients cancel the lower gaps

Write \(b_j=t_j-t_{j+1}\), \(t_7=0\). The exact forward bracket is
\[
 \gamma_{02}(L_{01}+L_{02}-4)
 +t_6^2 b_1(t_0-t_3)(L_{01}-2),\qquad
 \gamma_{02}=b_0b_2t_5t_6.
\]
If \(b_1>0\), the second line \(x_1\) has spectral gap at least \(h_1=\min(g,b_1)\), so its dephasing loss is at most \(d_1=\mathcal A\eta/h_1^2\). If \(d_1<1/2\), choose its largest-weight stabilizer basis vector, distinct from \(v_0\) by orthogonality. Otherwise any basis vector distinct from \(v_0\) gives squared infidelity at most \(1\le2d_1\). In both cases use (1), \(b_1/h_1\le1/g\), and \(t_0-t_3\le1\). The second term is at most \(29\sqrt2\,t_6^2\mathcal A\eta/g^2\). At \(b_1=0\) it vanishes.

If \(b_2>0\), the span \(P\) of \(x_1,x_2\) has gap at least \(h_2=\min(g,b_2)\) from the complementary eigenvalues. Its squared dephasing loss is at most \(d_2=\mathcal A\eta/h_2^2\) by the spectral commutator estimate for its projector. If \(d_2<1/4\), the two largest coordinate masses of \(P\) sum to at least \(2-d_2\), hence each exceeds \(3/4\). Neither is at \(v_0\), where the mass is at most \(e_0<1/4\). Let \(Q\) be their span. The polar isometry \(PQ(QPQ)^{-1/2}\) carries these two reference lines to an orthonormal basis of \(P\) with squared infidelities at most \(2d_2\), since \(\sqrt{QPQ}\succeq QPQ\) on \(Q\). If \(d_2\ge1/4\), any such distinct references and any orthonormal basis of \(P\) give errors at most one. In either case each error is at most \(4d_2\).

The sum \(L_{01}+L_{02}\) depends on \(P\) and the remaining flag, rather than the basis of \(P\). Every quadruple with first leg \(x_0\) is counted with weight equal to its number of indices in \(P\). At each fixed count the sum is the overlap trace on the appropriate exterior product of the subspaces, so it is invariant under changing the basis in \(P\). Apply (1) to both new basis vectors of \(P\). This gives \(L_{01}+L_{02}-4\le116\mathcal A\eta/(g h_2)\). Then \(\gamma_{02}\le b_2t_6\) and \(b_2/h_2\le1/g\) make the first term at most \(116t_6\mathcal A\eta/g^2\). At \(b_2=0\) it vanishes.

The whole bracket is at most \(160t_6\mathcal A\eta/g^2\) because \(t_6\le1\). If \(\eta\ge\eta_*\) use \(L_{ij}\le5/2\) and \(\gamma_{01}\le2t_6\) instead, giving a bracket at most \(2t_6\). Hence an admissible cutoff is
\[
 \varepsilon_{\rm top}(g)=\min\{\eta_*/336,\ g^2/(26880\mathcal A)\}.
\]
With the forward purity price \(168\) and actual defect at least \(\eta\), the excess is nonpositive. Two-frame Cauchy–Schwarz and stabilizer padding prove the physical claim. At a strict cutoff the paired defects of an optimizer both vanish, so its marginals are stabilizer-diagonal. For distinct nonzero probabilities the optimizing states are exactly the local Clifford images of the sorted state. [Forward coefficients](rank7_forward_coefficients_independent.md) · [Pauli defect and single-unitary reduction](https://arxiv.org/html/2609.13106v2)
