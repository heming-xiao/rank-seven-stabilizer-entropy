# Computational-basis optimality with one stabilizer Schmidt basis

November 17, 2026. This theorem restricts one marginal of the candidate state. It imposes no spectral or dimension restrictions.

## Statement

Let \(\psi\) be a bipartite pure qubit state and let \(\psi_\downarrow\) have the same Schmidt amplitudes in decreasing order on matching computational labels. Write
\[
F_\alpha(\psi)=\frac1{d_A d_B}\sum_{P,Q}
  |\langle\psi|P\otimes Q|\psi\rangle|^{2\alpha},
\qquad M_\alpha=\frac{\log_2 F_\alpha}{1-\alpha},
\]
using one Hermitian representative of each Pauli up to phase. For every integer \(\alpha\ge2\), if either reduced density matrix is diagonal in a Clifford image of the computational basis, then
\[
F_\alpha(\psi)\le F_\alpha(\psi_\downarrow).
\]
Thus the sorted representative minimizes \(M_\alpha\) over this restricted class at fixed Schmidt spectrum. If the nonzero Schmidt probabilities are distinct, equality holds exactly for local Clifford images of \(\psi_\downarrow\), up to global phase. With repeated probabilities, equality still forces the other marginal to be diagonal in a stabilizer basis.

## One-sided comparison

By Clifford invariance assume \(\rho_A\) is diagonal. Put \(V=\mathbb F_2^{n_A}\), \(I=\{x:\mu_x>0\}\), and write \(\psi=\sum_{x\in I}\mu_x|x\rangle|u_x\rangle\) with \(\mu_x>0\) and the \(u_x\) orthonormal in \(B\). The original placement of the amplitudes on \(V\) can be arbitrary. For \(a,b\in V\) use \(X^a Z^b\) on \(A\), discarding its Hermitian phase inside the absolute value. Set \(v_a(x)=\mu_x\mu_{x+a}\) and \(q_{a,Q}(x)=\langle u_{x+a}|Q|u_x\rangle\) wherever \(v_a(x)>0\). Then the Pauli expectation, up to that global phase, is
\[
s(a,b,Q)=\sum_{x\in V}(-1)^{b\cdot x}v_a(x)q_{a,Q}(x).
\]
Expand \(s^\alpha\bar s^\alpha\) and average over \(b\). Character orthogonality gives
\[
F_\alpha(\psi)=\sum_a\ \sum_{x_1+\cdots+x_{2\alpha}=0}
 \left(\prod_j v_a(x_j)\right)\operatorname{Re}K(a;\mathbf x),
\quad
K(a;\mathbf x)=\frac1{d_B}\sum_Q
 \prod_{j\le\alpha}q_{a,Q}(x_j)
 \prod_{j>\alpha}\overline{q_{a,Q}(x_j)}.
\]
Only positive-weight terms need to be defined. For any participating pair of unit vectors, Pauli Parseval gives
\[
\frac1{d_B}\sum_Q|\langle u_y|Q|u_x\rangle|^2
=\big\||u_x\rangle\langle u_y|\big\|_{\rm HS}^2=1.
\]
Since every Pauli is unitary, each modulus is at most one, hence its \(2\alpha\) moment in the same normalization is at most one. Hölder with \(2\alpha\) factors gives \(|K|\le1\). All outer weights are nonnegative, so
\[
F_\alpha(\psi)\le T_\alpha(\mu):=
\sum_a\ \sum_{x_1+\cdots+x_{2\alpha}=0}
        \prod_{j=1}^{2\alpha}\mu_{x_j}\mu_{x_j+a}.
\]
For aligned computational vectors in two copies of \(V\), only Paulis on \(B\) with shift \(a\) contribute. Their characters cancel by the XOR constraint and their phase cancels between the two halves of the product. There are exactly \(|V|\) such Paulis, so every \(K\) with positive weight is one. After sorting, all nonzero labels fit in both local dimensions. If \(B\) is smaller than \(A\), appending extra \(|0\rangle\) qubits to the sorted state on \(B\) leaves \(F_\alpha\) unchanged, because the moment factors on a product and is one for \(|0\rangle\). If \(B\) is larger, it is the original sorted state that has the fixed extra label bits zero. This identifies the aligned sorted expression with \(F_\alpha(\psi_\downarrow)\) on the original bipartition.

## Sorting by binary compression

Eliminate \(x_{2\alpha}\) to write \(T_\alpha\) as a sum over independent variables \(a,x_1,\ldots,x_{2\alpha-1}\) of products of the same nonnegative function at homogeneous binary linear forms \(L_j\). For any such sum and any nonzero binary direction \(\delta\), split \(V=H\oplus\langle\delta\rangle\), where \(H\) is the hyperplane whose highest bit set in \(\delta\) vanishes. Write
\[
\mu(q+\varepsilon\delta)=A(q)+(-1)^\varepsilon B(q),\qquad q\in H .
\]
Here \(A\) is the pair average and \(B\) is the signed half-difference. In every product, sum first over the direction bits of the independent variables. Only terms where the \(B\)-selected linear forms sum identically to zero survive, each with the same positive coefficient. Replacing \(B\) by \(|B|\) increases each surviving term since every \(A\) is nonnegative. This replacement moves the larger member of each \(\delta\)-pair to its lower label in \(H\). If the arrangement has an inversion \(x<y\) with \(\mu_x<\mu_y\), the compression for \(\delta=x+y\) strictly increases \(\sum_x(|V|-1-x)\mu_x\). Because there are finitely many arrangements, repeating such compressions sorts the amplitudes without decreasing \(T_\alpha\).

## Equality

Equality with the sorted representative forces equality at both stages. The repeated tuple \(x_j=x\) for all \(j\), with \(a=x+y\), has positive weight for each \(x,y\in I\). Its coefficient must attain one, so every \(|\langle u_y|Q|u_x\rangle|\) is zero or one. At \(x=y\), exactly \(d_B\) Paulis have modulus one by Parseval. They have a common eigenvector, so they commute and give a maximal commuting subgroup up to phases. Thus \(u_x\) is a stabilizer state. For any \(y\), Parseval for the pair provides a Pauli taking \(u_x\) to \(u_y\) up to phase. The Pauli orbit of a stabilizer state is its common stabilizer eigenbasis up to phases. This proves the second-marginal assertion even for missing labels or repeated amplitudes. The same argument gives the explicit purity gap
\[
 T_\alpha(\mu)-F_\alpha(\psi)
 \ \ge\ \sum_{x,y\in I}(\mu_x\mu_y)^{2\alpha}
 \left(1-\frac1{d_B}\sum_Q|\langle u_y|Q|u_x\rangle|^{2\alpha}\right).
\]

Suppose now that the \(r\) nonzero amplitudes \(\lambda_0>\dots>\lambda_{r-1}>0\) are distinct and put \(\lambda_r=0\). Write \(\mu=\sum_{k=1}^r c_k 1_{S_k}\), where \(S_k\) consists of the \(k\) largest labels by amplitude and \(c_k=\lambda_{k-1}-\lambda_k>0\). The compression proof works when each factor uses its own nonnegative function, with all functions compressed in the same direction. Moreover, compressing nested indicators \(1_{S_k}\) gives the prefix indicators for the compressed \(\mu\). This follows pair by pair: the same ordering of two amplitudes orders their membership in every prefix. Thus every coefficient of \(T_\alpha(\mu)\) as a polynomial in the \(c_k\) is nondecreasing along the same sorting chain. If equality holds at these strictly positive \(c_k\), all the coefficients agree with their sorted counterparts. The change of variables from the \(\lambda_j\) is invertible, so the polynomials in the individual ordered amplitudes agree as well.

For four distinct amplitude indices \(i,j,k,l\), the monomial \(\lambda_i^{4\alpha-6}\lambda_j^2\lambda_k^2\lambda_l^2\) has positive coefficient precisely when their labels form an affine plane. In the \(a=0\) part of the sum the four multiplicities of tuple entries are \(2\alpha-3,1,1,1\), all odd, so the sum of the four labels must vanish. A term with \(a\ne 0\) requires the four labels to be invariant under shift by \(a\), which also makes their sum zero. Conversely the tuple with \(a=0\) gives a contribution for every plane. Equality of polynomials therefore preserves every plane of the sorted prefix \(J=\{0,\ldots,r-1\}\).

An injective placement \(p:J\to\mathbb F_2^n\) preserving the planes of \(J\) is the restriction of an injective affine map on the \(m=\lceil\log_2 r\rceil\) bits spanned by \(J\) (with \(m=0\) for \(r=1\)). Every \(x\in J\) with two or more set bits is a sum \(x=u+v\) of two nonzero labels with disjoint bit supports. The labels \(0,u,v,x\) lie in \(J\) and form a plane, giving \(p(x)=p(0)+p(u)+p(v)\). Induction makes the values on \(0\) and on the bit vectors determine the placement. The lowest \(m-1\) bits range over a full subspace in \(J\) when \(m\ge1\), and injectivity on that subspace makes their image directions independent. The final bit vector has image outside that subspace by injectivity. A coordinate Clifford therefore aligns the placement on \(A\) with the sorted labels.

After a Clifford on \(B\), write \(u_x=z_x|p(x)\rangle\) for \(x\in J\), with distinct labels \(p(x)\) and unit phases \(z_x\). For any plane of \(J\), express its two parallel pairs as \((x,x+a),(y,y+a)\). Choose a tuple with \(x,y\) on each half, padded with copies of \(x\) on both halves if needed. The coefficient can equal one only if \(p(x+a)+p(x)=p(y+a)+p(y)\), since otherwise no Pauli acts nontrivially on both pairs. Hence \(p\) preserves the planes, and the same placement argument aligns the labels on \(B\).

To remove the phases, restrict first to any coordinate subcube \(V_L\subseteq J\) formed by all subsets of a bit set \(L\). Set \(w_a(x)=z_x\bar z_{x+a}\) on this cube. The tuple with \(x,y\) on the first half and \(0,x+y\) on the second, padded by the same labels on both halves, forces \(w_a(x)w_a(y)=w_a(0)w_a(x+y)\) for \(a,x,y\in V_L\). Thus \(w_a/w_a(0)\) is a binary character on \(V_L\). Taking \(x=a\) shows \(w_a(0)^2\in\{1,-1\}\), since \(w_a(a)=\bar w_a(0)\). Set \(z_0=1\) by a global phase choice and write \(z_x=i^{m(x)}\). The squared character relation makes \(m(x)\bmod2\) linear on each \(V_L\). Every \(x\in J\) lies in the cube generated by its set bits, so the parity is determined everywhere by its values on the bit vectors. Remove it by single-qubit \(S\) gates. The remaining signs are \((-1)^{g(x)}\) and the character relation makes all coordinate derivatives of \(g|_{V_L}\) affine. The square-free polynomial of \(g|_{V_L}\) therefore has degree at most two. On each cube its coefficients are determined by the common values of \(g\) at zero, singles and pairs. This gives a single quadratic polynomial extending \(g\) on \(J\), with any unused pair coefficients set to zero. Linear \(Z\) and quadratic \(CZ\) gates remove it. The converse follows from Clifford invariance.

## Relationship to earlier results

For the second-order unrestricted conjecture, see [Sierant, Conjecture 1](https://arxiv.org/html/2609.13106v2). The fixed-side portion of [Franchini–Giampaolo, §III.1](https://arxiv.org/html/2608.02745v2) covers a single qubit on that side and order two. The binary compression used here is the linear-configuration argument in [the sorting audit](root_audit_round2.md), in the setting of [Liu–Cui, Appendix C](https://arxiv.org/html/2609.01993v2). The unrestricted problem is equivalent, at each spectrum and order, to existence of an unrestricted minimizer with a stabilizer-basis diagonal marginal. The theorem gives the upper bound when this condition holds and leaves the existence question open.
