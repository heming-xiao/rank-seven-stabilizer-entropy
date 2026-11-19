# Uniform rank-seven neighborhoods of isolated leading doublets

November 17, 2026. Fix \(g>0\). For ordered positive Schmidt rank-seven probabilities \(t_0=1\ge t_1\ge\cdots\ge t_6\), assume
\[
 t_1-t_2\ge g,\qquad t_5-t_6\ge g .
\]
There is an explicit \(\varepsilon_{\rm lead}(g)>0\), independent of the qubit dimensions, such that \(t_6\le\varepsilon_{\rm lead}(g)\) guarantees the sorted computational representative is optimal over all local unitaries at order two. The first gap \(t_0-t_1\) and the gaps among \(t_2,\ldots,t_5\) may vanish. Thus every fixed rank-six spectrum whose highest eigenvalue is exactly double has a full rank-seven neighborhood, including arbitrary splitting of any of its repeated probabilities.

## Pauli rounding to two kinds of frames

Use the [dimension-independent Pauli extraction](rank7_generic_rank6_neighborhood.md) with \(R=7\) and parameter \(g\). In the unified high-coset formulation in [the manuscript](rank7_boundary_proof.tex), for \(\eta=\Delta_d(C)/d<\eta_*\) there are a commuting Pauli group \(G\), its averaging \(\mathcal E_G\), and a high-coset truncation \(C_{\rm hi}\) with
\[
 \|C-C_{\rm hi}\|_{\rm op}<5g/16,\qquad
 \|\mathcal E_GC-C_{\rm hi}\|_{\rm op}\le g/16,\qquad
 \|C-\mathcal E_GC\|_{\rm HS}^2\le\mathcal A\eta .
\]
Here \(C\) is the paired marginal probability matrix. The group \(G\) is not assumed maximal. Each character block has the same power-of-two dimension and \(C_{\rm hi}\) is scalar within those blocks.

Take the cutoff \(z=(t_5+t_6)/2\). Weyl's bound gives exactly six \(C_{\rm hi}\) eigenvalues above \(z\), all its eigenvalues being at least \(3g/16\) away from \(z\). Thus the block size divides six and is either one or two. Put \(D=\mathcal E_G C\). Its analogous upper spectral space \(Q\) is the same as for \(C_{\rm hi}\), since \(D\) respects the blocks and \(\|D-C_{\rm hi}\|<3g/16\).

If the block size is one then \(G\) is maximal. The [maximal-frame doublet payment](rank7_doublet_odd_cut_boundary.md) now applies directly: its remaining proof only uses \(t_1-t_2\ge g\), the full-frame dephasing bound, and the exact coefficients. It bounds the forward bracket by \(68\,t_6\mathcal A\eta/g^2\). It does not require an odd spectral cut once maximality is known.

## The two-dimensional blocks give a stationary reference

Suppose the block size is two. After a Clifford, \(Q\) is spanned by three binary coordinate cosets of the same one-dimensional subspace \(\langle a\rangle\). In the quotient by \(\langle a\rangle\), the three distinct points lie in one affine plane. Its preimage in the physical labels is an affine three-space \(H\) of eight points, with \(Q\) occupying all but the fourth coset \(E\). We also write \(H\) and \(E\) for their coordinate spans when used as vector spaces.

Let \(P\) be the actual leading six-dimensional subspace. For an eigenvector \(x_i\) of \(C\) above \(z\) and eigenvector \(u_j\) of \(D\) below \(z\), the eigenvalue equation gives
\[
 (t_i-\lambda_j)\langle u_j|x_i\rangle
  =\langle u_j|(C-D)x_i\rangle,\qquad t_i-\lambda_j\ge g/2 .
\]
Hence \(\operatorname{tr}P(I-Q)\le4\mathcal A\eta/g^2\).
Use the direct rotation \(e^K\) from \(Q\) to \(P\) in principal-angle bases. Its skew-Hermitian generator is off-diagonal in \(Q\oplus Q^\perp\): each principal two-plane has a standard plane rotation and the perpendicular remainder is fixed. For \(h=\|K\|_{\rm op}\), the principal angles in \([0,\pi/2]\) give
\[
 h^2\le(\pi^2/4)\|P-Q\|_{\rm HS}^2
       \le 2\pi^2\mathcal A\eta/g^2 <20\mathcal A\eta/g^2.
\]
Pull the seven actual vectors back by \(e^{-K}\). The first six are now in \(Q\), and the last vector is in \(Q^\perp\). Each fixed pair \(01\) or \(02\) is contained in \(H\), so both reference occupancies are at most two by the [affine-eight fixed-pair theorem](reviews/rank7_two_link_independent_review.md).

Along \(e^{sK}\) every \(L_{0i}\) has derivative zero at the reference. To verify this, projected coordinate four-wedges are resolved in the orthogonal stabilizer directions \(\psi_L\) indexed by the directions \(L\) of binary affine planes. Their signs do not affect the following disjoint support argument.

1. A wedge with four of the first six vectors has reference support only on planes in \(H\) whose direction contains \(a\): without \(a\) it would use all four cosets, but the vectors are in \(Q\). A single differentiated vector is in \(Q^\perp\). If outside \(H\), it cannot complete a plane with the three labels inside \(H\). If in \(E\), the plane visits \(E\) once, so its direction does not contain \(a\). Thus the derivative's projected support is disjoint from the reference support.
2. A wedge with the last vector and three of the first six has reference support only from its component in \(E\), with directions in \(H\) that avoid \(a\); the part outside \(H\) cannot complete a plane. If a leading vector is differentiated, the two factors in \(Q^\perp\) can both be in \(E\) (then any nonzero plane has direction containing \(a\)), one can be outside \(H\) (no plane), or both can be outside \(H\) (any plane direction is not contained in \(H\), because it also meets \(H\)). In each case the derivative has no reference directions. If the last vector is differentiated then it lies in \(Q\) and all four factors are in \(Q\), again giving only directions containing \(a\).

This proves zero derivative of each squared projection, independently of the basis of \(Q\) or the tail vector. By the standard one-hole bound \(q^{-1/2}\|\Pi_{\rm F}(u_1\wedge\cdots\wedge u_4)\|\le\prod_i\|u_i\|\), the normalized squared projection of a moving wedge has second derivative at most \(64h^2\) in absolute value. Each \(L_{ij}\) is the sum of ten such terms, so Taylor gives
\[
 (L_{0i}-2)_+\le320h^2\le6400\mathcal A\eta/g^2
 \qquad (i=1,2).
\]
The forward coefficients obey \(0\le\gamma_{02}\le\gamma_{01}\le2t_6\). The bracket is therefore at most \(25600\,t_6\mathcal A\eta/g^2\), which also dominates the maximal-group case.

For \(\eta\ge\eta_*\), use the universal \(L_{ij}\le5/2\) instead, giving bracket at most \(2t_6\). The actual purity excess is at most \(168\) times the bracket minus \(\eta\). It follows that one may take
\[
 \varepsilon_{\rm lead}(g)=\min\{\eta_*/336,\ g^2/(4300800\mathcal A)\}.
\]
The standard paired comparison and stabilizer padding give the conclusion on all physical bipartitions. For strict cutoff, equality forces commuting Pauli support on the two physical marginals, and for distinct positive probabilities the local Clifford equality classification follows. [Forward coefficient certificate](rank7_forward_coefficients_independent.md) · [Pauli defect and paired reduction](https://arxiv.org/html/2609.13106v2)

At a fixed rank-six spectrum with a leading doublet separated from the third probability, both \(t_1-t_2\) and \(t_5-t_6\) have positive limiting values, so sufficiently small perturbations preserve a fixed positive \(g\) and satisfy the tail cutoff. No lower multiplicity pattern is excluded.
