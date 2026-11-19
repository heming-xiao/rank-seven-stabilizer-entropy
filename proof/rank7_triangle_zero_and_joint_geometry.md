# Rigidity of the leading triangle and joint prices for its edges

Let \(D=2^n\ge8,\ m=D/2\), and let \(P\) be the projector onto any complex three-dimensional subspace. Write \(J_b=W_b\mathrm{conj}\) for the odd (skew) Pauli antiunitaries. The compression \(P J_b P\) is represented in orthonormal coordinates by a skew \(3\times3\) matrix followed by conjugation. Its two nonzero singular values are both \(\sqrt{r_b}\), where \(r_b=\sum_{i<j\le2}|\langle x_i,J_bx_j\rangle|^2\); when \(r_b=0\) the matrix is zero. Thus \(0\le r_b\le1\), and the complete odd Pauli frame gives \(m^{-1}\sum_b r_b=3\). Put \(\eta=m^{-1}\sum_b r_b(1-r_b)\), the third mixed-probe defect in the [triangle polarization](rank7_triangle_probe_tail_equalization.md).

**Rigidity theorem.** \(\eta=0\) if and only if \(P\) is a hyperplane of a rank-four stabilizer code. That code is unique. For any orthonormal extension to seven modes, every pair of leading modes satisfies \(L_{ij}\le2\).

## The common fourth line

At zero defect all \(r_b\) are zero or one. Exactly \(3m\) labels have \(r_b=1\). For each such label \(b\), the compressed skew antiunitary is an isometry on a plane in \(P\); its orthogonal kernel line has unit vector \(n_b\). The antiunitary preserves that plane and sends \(n_b\) to a unit vector \(t_b\in P^\perp\). If every kernel line were the same, every compressed skew form would vanish on its wedge with a second vector in \(P\), contradicting completeness of the odd Pauli basis.

Take two high labels with nonparallel kernel lines. Choose phases of the kernel vectors and one unitary coordinate system on \(P\) so they are real, \(n=e_3,\ m'=s e_2+c e_3\), \(s>0,\ s^2+c^2=1\). After separate phase changes of the two antiunitaries, their compressed skew matrices are the real cross-product matrices of \(n,m'\). Relative to \(P\oplus P^\perp\) their outgoing blocks have only their respective kernel columns, along \(t_b,t_{b'}\); their incoming blocks are determined by skew transposition. Consequently the compression of \(J_bJ_{b'}\) has matrix
\[
 m'n^{\mathsf T}-(n\cdot m')I+\zeta n(m')^{\mathsf T},\qquad
 |\zeta|=|\langle t_b,t_{b'}\rangle|.
\]
It is a phase times a Hermitian Pauli compression. Its \(23\) and \(32\) entries therefore have equal modulus: \(s=|\zeta|s\). The external lines coincide. If two kernels are parallel, use a third nonparallel kernel. All \(t_b\) thus span one line \(\mathbb C y\), and all high antiunitaries preserve \(T=P+\mathbb C y\), since \(J_b^2=-I\).

## Counting the invariant Paulis

Let \(G=\{a:W_aT=T\}\) in the binary Pauli label space and fix a high \(b_0\). The odd labels in \(b_0+G\) are precisely the high labels. Indeed an odd antiunitary preserving \(T\) sends its three-dimensional hyperplane \(P\) to another such hyperplane, with intersection of dimension at least two. The two singular values of \(P J_b P\) are then one. Conversely, every high antiunitary preserves \(T\).

If \(G\) has symplectic rank \(2k\), each irreducible Pauli representation for fixed radical character has dimension \(2^k\): diagonalize one member of each of the \(k\) conjugate Pauli pairs, and the other members biject all \(2^k\) joint eigenspaces. Since \(T\) has dimension four, \(k\le2\). On \(b_0+G\) the odd quadratic parity either occurs with density \(1/2\) or with density \((1\pm2^{-k})/2\). This follows by summing the parity character on the radical and then on the \(2k\)-dimensional nonsingular quotient. Its odd cardinality is \(3D/2\); the balanced value would force \(|G|=3D\), which is not a power of two. The remaining possibilities are
\[
 (k,|G|)=(1,2D)\quad\hbox{or}\quad (2,4D).
\]
In the first case the radical has size \(D/2\) and its character spaces have dimension two. Each is irreducible under \(G\), so \(T\) is the union of two such parallel rank-two codes. Their characters agree on an index-two subgroup, making their span a rank-four stabilizer code. In the second case the radical has size \(D/4\) and the character spaces are irreducible of dimension four, so \(T\) is a single such space.

Conversely each skew Pauli antiunitary permutes character codes of a given stabilizer, since complex conjugation of a Pauli changes only its sign. It either preserves a given rank-four code \(T\) or sends it to an orthogonal code. Hence a hyperplane \(P\subset T\) has \(r_b=1\) or \(0\) respectively. If another rank-four stabilizer code contains \(P\), every high antiunitary must preserve it, so it contains their common outside line and equals \(T\). The [fixed affine four-point bound](rank7_shared_anchor_twelve_and_anticommuting.md) gives \(L_{ij}-2\le18\operatorname{Tr}P_{ij}(I-T)=0\).

In this zero case the normalized one-hole completion is precisely the line \(y=T\ominus P\): after converting \(T\) to four affine coordinates, a four-wedge containing three points of \(T\) can be an affine plane only if its fourth point also belongs to \(T\). Thus \(w_{012i}=|\langle y,x_i\rangle|^2\). The three-head missing mass \(1-\sum_{i=3}^6 w_{012i}\) can already equal one at \(\eta=0\) by choosing all four remaining modes perpendicular to \(T\). A uniform positive lower price for \(\eta\) proportional to that missing mass alone is impossible.

## A simultaneous bound for three pair defects

Label the three leading pairs \(A,B,C\) in any order and put \(v_e=L_e-2\). For \(K=5/2\),
\[
 (v_C)_+\le K\min\{\kappa_C,\ \kappa_A+\kappa_B\},
 \qquad\kappa_i=m^{-1}\sum_b p_i(1-p_i). \tag{1}
\]
The first choice is the [individual code estimate](rank7_highest_pair_geometry_five_halves.md). If either \(\kappa_A,\kappa_B\ge2/15\), the second follows from \(v_C\le1/3\). Otherwise the individual code rounding gives rank-two stabilizer codes \(Q_A,Q_B\), and errors \(\epsilon_i=1-\operatorname{Tr}(P_iQ_i)/2\le(2000/6137)\kappa_i<1/20\) for \(i=A,B\). The common head vector \(x\) leaks at most \(2\epsilon_i\) out of each code; each stabilizing Pauli then has expectation of modulus at least \(1-4\epsilon_i>4/5\) on \(x\). All generators of both codes commute, since two anticommuting Paulis have squared expectations summing to at most one. The two codes cannot be orthogonal, since each contains more than one half of the mass of \(x\). They cannot coincide, since three mutually orthogonal physical legs would then have total mass greater than two in a two-dimensional code. In a common stabilizer basis the codes must be \(\operatorname{span}(s_0,s_1)\) and \(\operatorname{span}(s_0,s_2)\).

Let \(y,z\) be the two other head legs. Write \(u,v\) for the leakages of \(x,y\) outside \(Q_A\), and \(u',v'\) for the leakages of \(x,z\) outside \(Q_B\). Their total satisfies \(u+v+u'+v'=2(\epsilon_A+\epsilon_B)\). The mass of \(y,z\) outside the three lines \(s_0,s_1,s_2\) is at most \(v+v'\). Their combined mass on \(s_0\) is at most \(1-|\langle s_0,x\rangle|^2\le u+u'\), using orthogonality and the commuting code projectors. Thus the rank-two stabilizer code \(Q_C=\operatorname{span}(s_1,s_2)\) has \(\epsilon_C\le\epsilon_A+\epsilon_B\). The known fixed-code estimate gives \(v_C^+\le(13/2+\epsilon_C/2)\epsilon_C\le(13100/6137)(\kappa_A+\kappa_B)<2.14(\kappa_A+\kappa_B)\). This proves (1). The same proof works with the rational \(K=32/13\), using the extended small-defect cutoff in the individual geometry note and the same small-defect factor.

In the small-defect branch we also have
\[
 \kappa_C\le(8000/6137)(\kappa_A+\kappa_B).
\]
Indeed if the overlap amplitude of the physical wedge with the code wedge is \(a_C\), then the stabilizer code's odd coset contains squared wedge mass at least \(a_C^2\). Cauchy–Schwarz over its \(m\) labels gives \(1-\kappa_C\ge a_C^4\). The two squared cosines of the principal angles also give \(a_C^2\ge1-2\epsilon_C\). Therefore \(\kappa_C\le4\epsilon_C\).

Finally \(\sum_e v_e\le0\) holds on the original physical packing rows alone. In each four-wedge column the number of its leading vertices equals the number of tail vertices in the complementary triple. Counting pairs on both sides and using the six tail pair capacities gives \(\sum_e L_e\le6\). Individual positive excesses in (1) remain relevant under asymmetric spectral weights.
