# Optimality near all rank-six spectra with two separated leading probabilities

November 17, 2026. Fix \(g>0\). There is an explicit \(\varepsilon(g)>0\), independent of the local dimensions, with the following property. Suppose the seven nonzero Schmidt probabilities are scaled to
\[
 1=t_0>t_1>t_2\ge\cdots\ge t_6>0,\qquad
 \min(t_0-t_1,t_1-t_2)\ge g,\qquad t_6\le\varepsilon(g).
\]
Then sorting them on the computational labels minimizes order-two stabilizer Rényi entropy over arbitrary local unitaries. The probabilities \(t_2,\ldots,t_5\) need no other restrictions. Every fixed rank-six spectrum whose two largest probabilities are simple thus has a relative neighborhood of rank-seven spectra satisfying the full conjecture. This also applies at lower-rank boundary spectra with the same leading separation. With a strict cutoff and all nonzero probabilities distinct, the minimizers are precisely local Clifford images of the sorted representative.

## A commuting set of large Pauli coefficients

Let \(C\) be positive semidefinite of rank at most \(R\) and operator norm one on \(n\) qubits with dimension \(d=2^n\). Let \(c_W=\operatorname{tr}(CW)\) for Hermitian Paulis indexed by the binary symplectic space of size \(d^2\). Put \(\eta=\Delta_d(C)/d\), with \(\Delta_d\) the nonnegative Pauli defect. The two properties used below are
\[
 \frac1d\sum_W c_W^4
   \ge (\operatorname{tr}C^2)^2-\eta,\qquad
 \eta\ge\frac{4}{d^2}\sum_{\{W,W'\}\ {\rm anti}} c_W^2c_{W'}^2.
\]
For the first, use the definition of the defect, nonnegativity of the exterior overlap, and \(\operatorname{tr}C^4\le(\operatorname{tr}C^2)^2\). The second is its anticommuting sum bound. [Sierant, Eq. (101) and Theorem 14](https://arxiv.org/html/2609.13106v2)

Write \(\rho=1/(4R^4)\) and \(S=\{W:c_W^2>1/2\}\). If \(\eta\le1/4\), Pauli Parseval bounds the contribution of labels outside \(S\) to the normalized fourth moment by \((\operatorname{tr}C^2)/2\). Since \(\operatorname{tr}C^2\ge1\), the remaining contribution is at least \(1/4\). Also \(|c_W|\le\operatorname{tr}C\le R\). Hence \(|S|\ge \rho d\).

The number of ordered anticommuting pairs inside \(S\) is at most \(2\eta d^2\). Take \(k=\lceil24/\rho^2\rceil+1\) and \(\zeta=1/[16(k+1)]\). If \(\eta\le\zeta\rho^2/4\), the subset \(T\subseteq S\) of labels anticommuting with at most \(\zeta|S|\) other members of \(S\) has \(|T|\ge|S|/2\) by counting degrees. It includes the identity label zero. Every sum of at most \(k+1\) elements of \(T\) anticommutes with at most \((k+1)\zeta|S|\) members of \(S\), by the union bound on the symplectic characters. The unnormalized symplectic Fourier transform of \(1_S\) on each such sum is at least \(|S|/2\). Parseval gives
\[
 |(k+1)T|\le 4d^2/|S|\le 4d/\rho .
\]

Let \(V\) be the span of \(T\). If some element had minimum word length at least \(k\) in \(T\), take the first \(k\) steps of a shortest word. The translates of \(T\) by every third prefix would be disjoint: intersecting translates would express a difference of at least three steps by at most two. All would be contained in \((k+1)T\). This gives
\((\lfloor k/3\rfloor+1)|T|>4d/\rho\), a contradiction. Every element of \(V\) is therefore a sum of at most \(k\) labels from \(T\). Each anticommutes with at most \(|S|/16\) members of \(S\). Averaging over \(V\), each member of \(S\setminus V^\perp\) is counted with probability \(1/2\), so \(|S\setminus V^\perp|\le|S|/8\). Hence
\[
 B=T\cap V^\perp,\qquad |B|\ge 3|S|/8\ge3\rho d/8.
\]
This set commutes pairwise, since it lies in \(V\cap V^\perp\). Its individual coefficients still have squared modulus greater than \(1/2\).

## A commuting subgroup with uniformly small blocks

Let \(H=\langle B\rangle\), a commuting group modulo phases. Choose \(m=\lceil\log_2(8/\rho)\rceil\) and \(\beta=\rho/[16(m+1)]\). A character of \(H\) is sparse if it is negative on fewer than \(\beta d\) elements of \(B\). There cannot be \(m\) independent sparse characters: their common kernel in \(H\) would have size at most \(d/2^m\le\rho d/8\), but it would contain at least \(|B|-m\beta d>\rho d/8\) elements of \(B\). Set \(H'\) to the common kernel of the span of the sparse characters. Its joint eigenvalue blocks have dimension \(\ell=d/|H'|\le L=4\cdot2^m/\rho\).

A Pauli label outside the centralizer of \(H'\) induces a character of \(H\) that is nontrivial on \(H'\). Such a character cannot be sparse, so it anticommutes with at least \(\beta d\) members of \(B\). On \(B\) all \(c_W^2>1/2\). These pairs have one endpoint in \(B\subseteq (H')^\perp\) and one outside the centralizer. Thus the anticommuting defect and Parseval give
\[
 \|C-\mathcal E_{H'}C\|_{\rm HS}^2\le A\eta,\qquad A=\frac1{2\beta},
\]
where \(\mathcal E_{H'}\) is the average of conjugation by the Paulis in \(H'\).

## Round the two largest eigenlines to a common stabilizer basis

Suppose the top two eigenvalues are simple and \(\min(t_0-t_1,t_1-t_2)\ge g\). Set \(s=g/(16L)\), and \(\mathcal A=A+L/(4s^2)\). For now let
\[
 \eta<\eta_*=\min\{1/4,\zeta\rho^2/4,g^2/(16A),
                         2s^4/L^2,g^2/(4\mathcal A)\}.
\]
By the preceding dephasing bound, \(\mathcal E_{H'}C\) has a simple largest eigenvalue with gap at least \(g/2\), from Weyl's bound and \(\sqrt{A\eta}<g/4\). Choose a joint eigenspace \(Q\) of \(H'\) containing its top eigenvector. If \(\ell=1\), the group \(H'\) is already maximal.

Otherwise, for a logical Pauli label \(p\in (H')^\perp/H'\), let \(u_p=\operatorname{tr}(QCQ\,L_p)\) be the corresponding logical coefficient on \(Q\). The physical Pauli sums on its coset obey
\[
 \sum_{W\in p+H'}c_W^2\ge |H'|u_p^2
\]
by the character Parseval formula across the blocks. Consequently two anticommuting logical labels cost at least \(4u_p^2u_q^2/\ell^2\) in \(\eta\). The labels with \(|u_p|>s\) must commute pairwise, because \(\eta<2s^4/L^2\). Truncating \(QCQ\) to these coefficients changes the operator norm by at most \(\ell s\le g/16\), as there are at most \(\ell^2\) coefficients with expansion prefactor \(1/\ell\). The truncated matrix still has a simple largest eigenvalue. A matrix in a commuting Pauli group on \(\ell\) dimensions whose group is smaller than \(\ell\) has multiplicity at least two on every eigenvalue. Thus the high logical labels generate a maximal commuting logical group.

Lift this logical group to a maximal commuting physical group \(G\) containing \(H'\). Every label in \((H')^\perp\setminus G\) anticommutes with some high logical generator. Its entire coset contributes at least \(|H'|s^2\) in squared physical coefficients. These pairs can be counted without repetition by the endpoint outside \(G\). Applying the defect bound again gives
\[
 \|\mathcal E_{H'}C-\mathcal E_G C\|_{\rm HS}^2\le L\eta/(4s^2).
\]
When \(\ell=1\) take \(G=H'\). Either way, orthogonality of the nested Pauli projections gives \(\|C-\mathcal E_G C\|_{\rm HS}^2\le\mathcal A\eta\).

For either ordered top eigenline \(P_j\), the spectral gap from all other eigenvalues of \(C\) is at least \(g\). Entrywise in the spectral basis, \(\|[P_j,W]\|_{\rm HS}\le g^{-1}\|[C,W]\|_{\rm HS}\). Averaging the squared commutators over \(G\) shows
\(\|P_j-\mathcal E_G P_j\|_{\rm HS}^2\le \mathcal A\eta/g^2\).
This loss is one minus the sum of squares of the probabilities of the line in the basis of \(G\). The largest probability is at least that sum of squares. Thus each of the two top lines has squared infidelity at most \(\mathcal A\eta/g^2<1/4\) from a stabilizer basis vector. These two vectors must be different because the original eigenlines are orthogonal. For \(\eta\ge\eta_*\) the total squared infidelity from any pair is at most \(2\le2\eta/\eta_*\). Hence for all \(\eta\) one can choose a pair in the same stabilizer basis with
\[
 e_0+e_1\le K(g,R)\eta,\qquad K(g,R)=2/\eta_*+2\mathcal A/g^2 .
\]

## Application to rank seven

Take \(R=7\). The exact forward-gap inequality bounds the purity excess by
\[
 168\bigl[\gamma_{01}(L_{01}-2)+\gamma_{02}(L_{02}-2)\bigr]-\eta
\]
for \(0\le\gamma_{02}\le\gamma_{01}\) and
\(\gamma_{02}=b_0b_2t_5t_6\), \(\gamma_{01}=\gamma_{02}+t_6^2b_1(b_0+b_1+b_2)\).
Here \(b_i=t_i-t_{i+1}\), and \(t_7=0\). Since \(t_0=1\), \(\gamma_{01}\le t_6+t_6^2\le2t_6\). The paired anchor estimate with \(\lambda=\gamma_{02}/\gamma_{01}\) bounds the bracket by \(126500\gamma_{01}K(g,7)\eta\); when \(\gamma_{01}=0\) the bracket is zero. Therefore
\[
 \varepsilon(g)=\frac{1}{336\cdot126500 K(g,7)}
\]
suffices. The standard two-sided reduction and stabilizer padding show the result for arbitrary bipartitions. The strict case forces \(\eta=0\) for each maximizing one-frame objective, so the physical marginals have commuting Pauli support (the support embeds by tensoring identity when padded). The all-rank rigidity result for distinct nonzero probabilities then gives the claimed Clifford equality. [Forward-gap certificate](rank7_forward_coefficients_independent.md) · [Anchor compensation](rank7_single_anchor_quadratic_astra.md) · [Rigidity](one_stabilizer_marginal_optimality.md)

The sufficient cutoff is chosen for a uniform analytic proof. The extension from any fixed generic rank-six boundary does not depend on a cutoff of practical numerical size.
