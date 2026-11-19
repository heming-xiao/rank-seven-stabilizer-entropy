# A low-defect exclusion theorem for rank-seven interior spectra

November 17, 2026. Normalize the ordered positive eigenvalues of the paired rank-seven probability matrix \(C\) by \(t_0=1\). For every lower bound \(s>0\) on \(t_6\), there is an explicit dimension-independent \(\delta(s)>0\) such that
\[
 t_6\ge s,\qquad \eta=\Delta_d(C)/d\le\delta(s)
 \quad\Longrightarrow\quad c_{\rm F}(C)\le c_{\rm F}(C_{\rm CB}).
\]
Consequently the paired stabilizer purity is no greater than the sorted computational-basis value. The result has no spectral-gap or multiplicity condition among the seven positive eigenvalues. Any paired counterexample in this spectral range must have normalized Pauli defect greater than \(\delta(s)\).

## Direct comparison when the support leaks only slightly out of an affine eight-space

Let \(H\) be the coordinate span of any affine binary three-space in the physical labels and \(\xi=\operatorname{tr}(C P_{H^\perp})\). The following comparison needs no defect hypothesis:
\[
 t_6\ge s,\quad \xi\le s^3/560
 \quad\Longrightarrow\quad c_{\rm F}(C)\le c_{\rm F}(C_{\rm CB}).
 \tag{1}
\]
To see this, let \(x_i\) be the eigenbasis on the support and decompose \(v_i=\sqrt{t_i}\,x_i=h_i+o_i\) into \(H\) and its complement. Put \(\delta_i=\|o_i\|^2\), so \(\sum_i\delta_i=\xi\) and all \(\|v_i\|\le1\). All wedge projections in this proof are normalized by \(\sqrt q\), with \(q=4/d\). By the one-hole isometry their norm is at most the product of the four vector norms.

For each four-set of eigenvectors, write its normalized projected wedge as \(A+B\), with \(A\) the all-\(H\) term. Exactly one outside leg gives zero by binary XOR. Hence \(B\) has at most eleven terms, all with at least two outside legs. The reference \(A\) has only directions in the linear space of \(H\). Among terms of \(B\) only the all-outside term can have such a direction: a plane parallel to \(H\) that meets \(H\) is entirely inside \(H\). Thus the cross term in the squared norm is at most twice the product of the four outside norms.

In the sum over all four-sets, squared norms of terms with exactly \(k\) outside legs sum to at most \(\binom{7-k}{4-k}e_k(\delta)\), where \(e_k\) is the elementary symmetric sum. Since \(e_k(\delta)\le \xi^k/k!\) and \(\xi\le1\), Cauchy–Schwarz over the eleven terms gives
\[
 \sum\|B\|^2\le 11(5+2/3+1/24)\xi^2 .
\]
Also \(\sum_i\sqrt{\delta_i}\le\sqrt{7\xi}\), so twice the sum of the four-outside products is at most \(98\xi^2/24\). Adding yields
\[
 \frac{c_{\rm F}(C)-c_{\rm F}(P_H C P_H)}q\le70\xi^2 .
 \tag{2}
\]
The sum of the squared all-\(H\) terms equals the exterior overlap of \(P_H C P_H\) by the determinant (exterior Cauchy–Binet) expansion; no orthogonality of the projected \(h_i\) is needed.

Let \(\lambda_i\) be the seven largest eigenvalues of the compression to \(H\). They satisfy \(\lambda_i\le t_i\) by the variational principle, and \(\sum_i(t_i-\lambda_i)=\xi\), so \(\lambda_6\ge s-\xi\ge s/2\). Within \(H\) the normalized coordinate Pauli-plane projection agrees with the three-qubit version, by Clifford covariance and pure computational padding. The established rank-seven eight-dimensional overlap theorem bounds \(c_{\rm F}(P_H C P_H)/q\) by the affine-plane polynomial at the sorted \(\lambda_i\). Each of the seven labels belongs to a reference plane. On increasing \(\lambda\) to \(t\) coordinatewise, the derivative of this polynomial with respect to any entry is at least \((s/2)^3\). Thus the compressed overlap is below the sorted reference by at least \(q(s/2)^3\xi\). The bound \(\xi\le s^3/560\) pays (2), proving (1). [Eight-dimensional overlap comparison](rank7_fano_proof.md) · [One-hole isometry](https://arxiv.org/html/2609.13106v2)

## A uniform diagonal margin outside affine eight-spaces

For a set \(S\) of seven binary labels let \(m_a\) be the number of unordered pairs in \(S\) with nonzero difference \(a\). Then \(m_a\le3\), \(\sum m_a=21\), and three times its affine-plane count is \(\sum_a\binom{m_a}{2}\le21\). For equality every realized difference has multiplicity three. Translate so \(0\in S\). Then \(S+S\) consists of \(S\) and one extra label \(p\); for every nonzero \(x\in S\), the union of \(S\) and \(S+x\) is precisely \(S+S\). Because translation by \(x\) swaps these two sets, it preserves \(S+S\). Thus \(S+S\) is preserved by the whole span of \(S\), contains zero, and is contained in that span. It is an eight-point linear space. In particular a support outside affine eight-spaces contains at most six affine planes.

For any placement of the seven probabilities on a support \(S\), write the plane polynomial \(\sum_{\text{affine } A\subset S,\,|A|=4}\prod_{i\in A}t_i\). Its sorted computational value dominates coefficientwise in the forward gaps \(b_j=t_j-t_{j+1}\) (with \(t_7=0\)). Indeed, the scalar additive energy \(\sum_{x+y+z+w=0}f(x)f(y)f(z)f(w)\) is the sum of a repeated-index spectral term and 24 times the plane polynomial. Expand \(f\) in the nested top-level indicators with coefficients \(b_j\). Binary compressions of the nonnegative nested functions simultaneously increase every mixed linear-configuration count, hence every coefficient. They sort the placement. The repeated-index term is spectral and cancels identically. When only \(b_6\) is nonzero, the coefficient is the plane count. Since the sorted support has seven planes, for a diagonal arrangement \(C_{\rm diag}\) on a nonaffine support one obtains
\[
 c_{\rm F}(C_{\rm CB})/q-c_{\rm F}(C_{\rm diag})/q\ge t_6^4\ge s^4 .
 \tag{3}
\]
[Mixed binary compression](one_stabilizer_marginal_optimality.md)

## Pauli rounding and explicit threshold

Apply the high-coset extraction from the [rank-six boundary proof](rank7_every_rank6_boundary.md) with rank bound seven and gap parameter \(g=s\). At \(\eta<\eta_*\) the truncation \(C_{\rm hi}\) is within \(5s/16\) in operator norm of \(C\), is scalar on the common character blocks of a commuting Pauli group \(G\), and satisfies
\[
 \|C-D\|_{\rm HS}^2\le \mathcal A\eta,\qquad
 D=\mathcal E_G C,\qquad \|D-C_{\rm hi}\|\le s/16 .
\]
The count at the cutoff \(t_6/2\) is seven for \(C_{\rm hi}\), so its odd multiplicity forces \(G\) maximal. It has the same upper seven-space \(Q\) as \(D\), because the character blocks are preserved and the cutoff margin is at least \(3s/16\). Write \(P\) for the support of \(C\). The spectral residual bound gives
\(\operatorname{tr}P(I-Q)\le4\mathcal A\eta/s^2\).
If \(Q\) lies in \(H\), the leakage of \(C\) out of \(H\) is at most this because \(C\preceq P\). The bound \(\eta\le s^5/(2240\mathcal A)\) permits (1).

Otherwise let \(C_{\rm diag}\) have the original seven probabilities on the leading seven coordinates of \(D\), in the order of the eigenvalues of \(D\). The Hoffman–Wielandt inequality gives \(\|C_{\rm diag}-D\|_{\rm HS}\le\|C-D\|_{\rm HS}\), so \(\|C-C_{\rm diag}\|\le2\sqrt{\mathcal A\eta}\). The two supports together span a space of dimension at most 14. On its four-exterior space the compression of \(\Pi_{\rm F}\) is positive with trace at most \(q\binom{14}{4}\), again by the unit-wedge bound. The difference of the two fourth exterior powers has operator norm at most \(4\|C-C_{\rm diag}\|\) by telescoping the fourth tensor powers of contractions. Hence
\[
 |c_{\rm F}(C)-c_{\rm F}(C_{\rm diag})|/q\le8008\sqrt{\mathcal A\eta}.
\]
This clears the diagonal margin (3) when \(\eta\le s^8/(16016^2\mathcal A)\).

An admissible tolerance is therefore
\[
 \delta(s)=\min\{\eta_*/2,\ s^5/(2240\mathcal A),\ s^8/(16016^2\mathcal A)\}.
\]
The rank-seven compression \(Q_{(1^4)}\le q c_{\rm F}\) and the nonnegative actual defect establish the stated paired-purity bound. If a physical bipartition has both paired defects below the threshold, the geometric-mean comparison gives the same conclusion. This is an exclusion for low-defect frames; larger-defect frames remain to be controlled. [Paired comparison and rank-seven compression](https://arxiv.org/html/2609.13106v2)
