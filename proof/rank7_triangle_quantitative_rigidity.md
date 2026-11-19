# Quantitative rigidity of the triangle probe in arbitrary qubit dimension

For every physical seven-frame and each of its three leading pairs \(e\), the triangle defect \(\eta=\langle r_b(1-r_b)\rangle\) controls the positive exterior excess:
\[
  (L_e-2)_+\le 200704000\,\eta .
  \tag{1}
\]
For \(\eta\le\eta_0=1/(50176\cdot12000)\) the stronger estimate \( (L_e-2)_+\le10\eta\) holds. These conservative global constants give a dimension-free positive price on each individual excess from the coefficient of \(\eta\) in the actual triangle-probe payment. In the sum of payments one allocates that coefficient once, for example to the largest positive \(L_e-2\). The joint pair-defect prices can be retained from the other coefficients. Notation follows the [zero-defect theorem](rank7_triangle_zero_and_joint_geometry.md).

## A uniformly concentrated outside line

For \(r_b>0\) let \(n_b\) be a unit kernel vector of the compressed skew Pauli on the leading three-space \(P\); \(t_b=J_b n_b\) is a unit vector in \(P^\perp\). Set \(\delta_b=1-r_b\). For each pair of these labels we have
\[
 (1-|\langle n_b,n_c\rangle|^2)(1-|\langle t_b,t_c\rangle|^2)
 \le40(\delta_b+\delta_c). \tag{2}
\]
Use the coordinates and phases of the exact proof: \(n=e_3,\ m=s e_2+c_0e_3\) are real, \(s\ge0\). In the compressed product of the two Paulis the internal term is \(\sqrt{r_b r_c}(mn^{\mathsf T}-(n\cdot m)I)\). The outgoing block of the first antiunitary maps its kernel to \(t_b\), and on the perpendicular plane has norm \(\sqrt{\delta_b}\) and image orthogonal to \(t_b\); the second has the same decomposition. By skew transposition their external product is \(\zeta n m^{\mathsf T}\), \(|\zeta|=|\langle t_b,t_c\rangle|\), plus an error of norm at most
\[
 (\sqrt{\delta_b}+\sqrt{\delta_c})\sqrt{1-|\zeta|^2}
       +\sqrt{\delta_b\delta_c}.
\]
Indeed each single-error product tests one outside line against the other line's orthogonal complement. Comparing the moduli of entries 23 and 32 in the phase-Hermitian compressed product gives \(s|\sqrt{r_b r_c}-|\zeta||\) at most twice the displayed error. With \(u=\delta_b+\delta_c\) and \(T_0=1-|\zeta|^2\), use \(1-\sqrt{r_b r_c}\le u\) and \(1-|\zeta|\ge T_0/2\). This gives \((s^2/2)T_0\le2u+2\sqrt{2u\,s^2T_0}\). For \(u>0\) the quadratic root is \(s\sqrt{T_0/u}\le2\sqrt2+2\sqrt3<\sqrt{40}\); the same inequality also covers \(u=0\).

Give the labels probability \(\mu_b=r_b/(3m)\), \(m=D/2\), omitting zeros. Their normal lines have mean projection \(I_P/3\): the three-dimensional Hodge map carries the odd Pauli two-form coefficients into \(\sqrt{r_b}\,n_b\) up to conjugation and phase, and the odd two-forms are a complete orthonormal basis. Equivalently the restricted skew frames on \(\Lambda^2P\) resolve its identity. Also \(\mathbb E_\mu\delta_b=\eta/3\). For any \(b,c\), an independent label \(i\) simultaneously has squared normal overlaps with \(b,c\) at most \(5/6\) with probability at least \(1/5\), by Markov and the union bound. Among these \(i\) one has \(\delta_i\le5\eta/3\). The distance of two line projectors in operator norm is the sine of their angle. Its triangle inequality and (2) imply
\[
  1-|\langle t_b,t_c\rangle|^2
  \le480(\delta_b+\delta_c+10\eta/3).
\]
Averaging over \(b,c\) bounds the mean by \(1920\eta\). Select one of the outside lines \(y\) with \(\mathbb E_\mu[1-|\langle y,t_c\rangle|^2]\le1920\eta\).

This weighted outside-line ensemble is exactly the normalized one-hole completion density \(R_\omega\) for the unit volume \(\omega\) of \(P\):
\[
 \langle z,R_\omega z\rangle=(4/D)^{-1}\|\Pi_F(\omega\wedge z)\|^2,
 \qquad R_\omega=\mathbb E_\mu |t_b\rangle\langle t_b| .
\]
Indeed the [squared-skew-form tight frame](reviews/rank7_two_link_independent_review.md) expresses the left-hand side as \((3m)^{-1}\) times the sum of squared four-by-four Pfaffians. In a basis of \(P\) whose third vector is \(n_b\), the Pfaffian for \(b\) has squared modulus \(r_b|\langle t_b,z\rangle|^2\); at \(r_b=0\) it vanishes. Thus \(\lambda_{\max}(R_\omega)\ge1-1920\eta\). A principal eigenvector may be chosen for \(y\) above; then for every tail projection \(Z\),
\[
 \left|\operatorname{Tr}(Z R_\omega)-\|Zy\|^2\right|\le1920\eta .
\]
The positive and negative parts of \(R_\omega-|y\rangle\langle y|\) both have trace \(1-\lambda_{\max}\), proving the claim even for large \(\eta\).

## Rounding the resulting four-space

Put \(T=P+|y\rangle\langle y|\) and \(\ell_b=4-\operatorname{Tr}(T J_b T J_b^\dagger)\). The internal skew weight of \(T\), counting unordered pairs, is at least \(r_b+|\langle y,t_b\rangle|^2\) for every positive-weight label. Thus
\[
 \langle r_b\ell_b\rangle\le2(\eta+3\cdot1920\eta)\le M\eta,\qquad M=12000.
\]
Assume \(0<\eta\le\eta_0\). Let \(A\) be the odd labels with \(\ell_b\le4M\eta\). Their \(r\)-mass is at least \(3-1/4\); hence \(|A|\ge11D/8\). Choose \(b_0\in A\), set \(T_0=A+b_0\) in the binary label space and \(H=\operatorname{span}T_0\). Each generator \(a\in T_0\) has \(\|T-W_aTW_a\|_{\mathrm{op}}\le4\sqrt{M\eta}\) by composing two skew antiunitaries, each moving the projection by at most \(\sqrt{\ell_b}\). Every element of \(7T_0\) therefore has projection distance at most \(28\sqrt{M\eta}\le1/8\). Pauli averaging gives \(\sum_a\operatorname{Tr}(TW_aTW_a)=16D\). Each of those approximate symmetries contributes at least \(4(1-1/64)\); hence \(|7T_0|\le4D/(1-1/64)<3|T_0|\).

If a shortest word for some element of \(H\) had length at least six, the prefixes at lengths zero, three, and six would give disjoint translates of \(T_0\) in \(7T_0\). An intersection would shorten a subword of length at least three to at most two. Therefore \(H=5T_0\) and \(|H|\) is \(2D\) or \(4D\). Every \(H\)-conjugate of \(T\) is within \(e=20\sqrt{M\eta}<1/2\) of \(T\). The group average has exactly four eigenvalues above \(1/2\); let \(Q\) be their projector. It commutes with \(H\) and \(\|Q-T\|_{\mathrm{op}}\le e/(1-e)\le2e\). For example on the low eigenspace the inverse of one minus the average has norm at most \(1/(1-e)\); apply it to the residual of \(T\).

The symplectic rank of \(H\) is \(2k\le4\) since it has the invariant four-space \(Q\). A subgroup with this symplectic rank has size at most \(2^kD\), as its radical and one member of each conjugate pair generate an isotropic subgroup. For \(|H|=4D\) this forces \(k=2\). For \(|H|=2D\) and \(k=2\), the odd density on \(b_0+H\) is at most \(5/8\), by the quadratic Gauss count, giving at most \(5D/4<|A|\) odd labels. Hence \(k=1\) when \(|H|=2D\). As in the exact proof, the first branch gives one full four-dimensional stabilizer character block and the second gives the span of two parallel two-dimensional blocks. Both are rank-four stabilizer codes.

## Improving the small-defect constant

The leakage \(\xi=\operatorname{Tr}P(I-Q)\le3(2e)^2\le4800/50176<1/8\). An odd label either preserves \(Q\) or sends it orthogonally away. For the latter labels \(r_b\le4\xi\): for each pair \(i,j\) the core-core matrix element is zero, and the remaining amplitude is at most \(\sqrt{\epsilon_i}+\sqrt{\epsilon_j}\), with \(\epsilon_i=\|(I-Q)x_i\|^2\). Sum its square over the three pairs.

The normalized Pauli wedge basis on labels preserving \(Q\) only has components with both legs in the same character block of the code stabilizer. In particular these two-forms have zero component on \(Q\wedge Q^\perp\). For an orthogonal pair \(x_i,x_j\), the mass of \(x_i\wedge x_j\) on \(Q\wedge Q^\perp\) is at least \(\epsilon_i+\epsilon_j-2\epsilon_i\epsilon_j\): the omitted cross term is \(2|\langle Qx_i,Qx_j\rangle|^2\ge0\). Completeness of the basis now gives
\[
 \langle r_b\,\mathbf1_{J_b Q\perp Q}\rangle\ge 2\xi-\xi^2,\qquad
 \eta\ge(1-4\xi)(2-\xi)\xi .
\]
Initially this gives \(\xi\le2\eta\); throughout the small-defect range this implies \(\xi<1/100\). A second application yields \((1-4\xi)(2-\xi)>9/5\). The [fixed-code estimate](rank7_shared_anchor_twelve_and_anticommuting.md) gives \(v_e\le18\xi\le10\eta\) for every pair. At \(\eta=0\) use the exact classification, and at \(\eta>\eta_0\) the physical \(v_e\le1/3\) gives the coefficient \(1/(3\eta_0)=200704000\). This completes (1). The smallness threshold comes from approximate Pauli group rounding; practical prices away from that regime still benefit from combining the three incident-pair bounds.
