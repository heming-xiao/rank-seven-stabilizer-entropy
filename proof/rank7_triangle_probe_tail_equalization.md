# Tail-edge prices and the mixed probe on the leading triangle

November 18, 2026. Let the seven positive probabilities be \((\alpha,\beta,\gamma,a,b,c,d)\) in descending order. A tail-edge price improves the mixed estimates for every spectrum. A second price gives a third mixed probe with zero reference cost on the subregion \(\gamma(a-b)\ge c(a-d)\). Odd cuts at ranks five and seven supply a separate anticommuting payment on the full space of spectra. All these bounds leave the actual exterior compression available.

Write \(h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a,\ g=hq,\ \Delta=k(\alpha-a),\ j=(\beta-c)(\gamma-b),\ H=b(c-d)\). For each skew Pauli let \(p_{ij}=|\langle x_i,Jx_j\rangle|^2\), \(p_1=p_{01}\), \(p=p_{01}+p_{02}\), \(r=p+p_{12}\). The normalized sum is \(\langle f\rangle=(2/D)\sum f\), with \(D\) the ambient qubit dimension. The matching bound on three vertices gives \(0\le p_1\le p\le r\le1\), with respective masses \(1,2,3\). Put \(s_6=\sum_{i<j\le5}p_{ij}\). Let \(u_1,u,w\) be the real mixed projections of the nested two-wedge subspaces indexed by \(\{01\},\{01,02\},\{01,02,12\}\). In particular \(w=\mathcal B\Lambda^2P_3\), where \(P_3\) is the leading single-particle three-space. Let \(U_1,U,U_\triangle\) be the weighted occupancies of these three edge families minus their Fano reference values, using weight \(t_{I\setminus e}\) for a four-wedge \(I\supset e\). For the third probe the combined reference is \((\alpha+\beta+\gamma)a+bc+bd+cd\). [Conditional matching and mixed normalization](rank7_general_two_probe_matching.md)

All three selected edges intersect each other. The four-wedge cross term in their pairwise polarization vanishes, giving the exact Gram quantities
\[
 \begin{array}{lll}
 2\|u_1\|^2=\kappa_1=\langle p_1(1-p_1)\rangle,&
 2\|u\|^2=\kappa=\langle p(1-p)\rangle,&
 2\|w\|^2=\eta=\langle r(1-r)\rangle,\\
 2\langle u_1,u\rangle=c_1=\langle p_1(1-p)\rangle,&
 2\langle u,w\rangle=\lambda=\langle p(1-r)\rangle,&
 2\langle u_1,w\rangle=\lambda_1=\langle p_1(1-r)\rangle .
 \end{array}\tag{1}
\]
All entries are nonnegative. The notation \(L=L_-(C)\) below refers to the actual mixed projection.

## One tail-edge price for every spectrum

Put \(\rho=\min\{H,\,(\gamma-c)(a-b)\}\) and \(j_s=j-\rho\ge0\). Subtract \(\rho\) from the edge \(45\) in each seven-mode matching. In any of the three types containing a leading edge \(01,02,12\), subtract \(\rho\) also from its conditional optimum \(M_{\rm type}\); the fourth type keeps its previous upper bound. The charge for missing edges and using the final vertex changes from \(H\ell\) to \((H-\rho)\ell\), where \(\ell=3-\#\{\text{edges entirely inside }0,\dots,5\}\).

To check the inequality, start with the earlier pointwise charge \(M_{\rm type}-\mathrm{score}\ge H\ell\). Its available slack increases by \(\rho(\ell+\mathbf1_{45}-\mathbf1_{\rm leading})\). The sole potentially negative case has one leading edge, \(\ell=0\), and omits \(45\). Its four remaining vertices have weights \(z,a,b,c\) with \(z\ge\gamma\). Replacing the leading pairing \(za+bc\) by the best alternative \(zb+ac\) loses \((z-c)(a-b)\ge\rho\). On averaging over the matching representation at one Pauli, the corrected upper bound is
\[
 s_C\le M_{02}-\rho+\Delta p_1-g(1-p)
       -j_s(1-r)-(H-\rho)(3-s_6)+\rho p_{45}.
\]
Multiplying by \(p\) and applying the exact mixed polarization yields
\[
 2\langle u,L\rangle\ge U+\Delta c_1+g\kappa+j_s\lambda
 +(H-\rho)(5-\langle p s_6\rangle)+\rho(1-\langle p p_{45}\rangle).
\]
The final term is nonnegative since \(p\le1,\ \langle p_{45}\rangle=1\). Both tail corrections vanish at the reference: the XOR direction of \(45\) is that of \(01\). Using the established \(\langle p s_6\rangle\le5+\Lambda\kappa\), with \(\Lambda=200/11\) uniformly or \(2\) in the small-defect branch, gives
\[
 2\langle u,L\rangle\ge U+\Delta c_1+G\kappa+j_s\lambda,\qquad
 G=g-\Lambda(H-\rho). \tag{2}
\]
When \((\gamma-c)(a-b)\ge b(c-d)\) the full coefficient \(g\) is available, including on spectra with four distinct tail values. [Geometric six-mode bound](rank7_four_level_1231_packing.md)

Multiplying the same pointwise inequality by \(p_1\) gives
\[
 2\langle u_1,L\rangle\ge U_1+\Delta\kappa_1+gc_1+j_s\lambda_1
 +(H-\rho)\langle p_1(3-s_6)\rangle+\rho(1-\langle p_1p_{45}\rangle).
\]
The final overlap obeys \(2(1-\langle p_1p_{45}\rangle)=
\kappa_1+\kappa_{45}+\langle(p_1-p_{45})^2\rangle\), with \(\kappa_{45}=\langle p_{45}(1-p_{45})\rangle\). Thus for every spectrum
\[
 2\langle u_1,L\rangle\ge U_1+(\Delta+\rho/2)\kappa_1+gc_1
                        +j_s\lambda_1+(\rho/2)\kappa_{45}. \tag{3}
\]
The former highest-pair price with \(j\lambda_1\) also remains individually available.

## Three simultaneous probes with no additive reference loss

Suppose
\[
                    \gamma(a-b)\ \ge\ c(a-d). \tag{4}
\]
In the matching score subtract \(\rho_{45}=c(b-d)\) on edge \(45\) and \(\rho_{46}=d(b-c)\) on edge \(46\). The three internal edges on tail vertices \(4,5,6\) now all cost \(cd\). If a leading edge is fixed and the remaining leading weight is \(z\ge\gamma\), the best completion costs \(za+cd\). Indeed a matching omitting either \(z\) or \(a\) costs at most \(ab+cd\) or \(zb+cd\). When both occur and are separated, its score is at most \(zb+ac\), which (4) bounds by \(za+cd\). A partial matching can be extended to two edges as all residual prices are nonnegative. For the type without a leading edge use its old maximum, attainable by matching the three heads to \(a,b,c\). Consequently all three leading conditional optima decrease by \(\rho_{45}\), and the third consecutive gap becomes \(j_t=j-\rho_{45}\ge0\). The last inequality follows from \(\rho_{45}\le(\gamma-c)(a-b)\le j\).

Multiply this new pointwise inequality by \(r\). Each added-back edge moment is at most one, since \(r\le1\) and each edge has normalized mass one. Both attain one at the reference, since the XOR directions of \(45,46\) are precisely \(01,02\). Thus
\[
 2\langle w,L\rangle\ge U_\triangle+\Delta\lambda_1+g\lambda+j_t\eta
 +\rho_{45}(1-\langle r p_{45}\rangle)
 +\rho_{46}(1-\langle r p_{46}\rangle). \tag{5}
\]
The unrestricted bound
\(2\langle w,L\rangle\ge U_\triangle+\Delta\lambda_1+g\lambda+j\eta-H-c(b-d)\)
follows from the original matching and \(s_6\le3\). Its additive price can obstruct a signed certificate near the reference. Condition (4) supplies a zero-cost alternative. The completion \(zb+ac\) shows exactly where this two-edge price stops proving (5).

For a single actual mixed norm, expand the square \(\|L-su-tu_1-zw\|^2\). Choose \(s=G_+=\max(G,0)\), \(t=\Delta\), and \(0\le z\le2j_t\). On (4), \(G=g\); it is convenient to keep the notation \(s\) to display the cross coefficients. Equations (2), (3), (5) imply
\[
\begin{aligned}
 24\|L\|^2\ \ge {}&
 24sU+24\Delta U_1+24zU_\triangle
 +12s^2\kappa+(12\Delta^2+12\Delta\rho)\kappa_1
 +12z(2j_t-z)\eta+12\Delta\rho\,\kappa_{45}\\
 &+24\Delta g c_1+24[sj_s+z(g-s)]\lambda+24\Delta j_s\lambda_1 .
\end{aligned}\tag{6}
\]
The three cross prices are nonnegative. On every spectrum, using \(z=0\) and the first two probes gives (6) with the \(z\) terms deleted, without imposing (4). From (1), \(\kappa_{02}=\kappa+\kappa_1-2c_1\) and \(\kappa_{12}=\eta+\kappa-2\lambda\). For converting (6) to linear prices on the exterior occupations, each \(\kappa_e\) satisfies \(K\kappa_e\ge (L_e-2)_+\), \(K=5/2\), and \(12\kappa\ge(L_{01}+L_{02}-4)_+\). These inequalities can be used together with their exact Gram relations. [Single-edge bound](rank7_highest_pair_geometry_five_halves.md) · [Shared-edge bound](rank7_shared_anchor_twelve_and_anticommuting.md)

## Independent anticommuting payment from odd tail cuts

Let \(P_i\) project on the largest \(i\) spectral modes, and let \(J_{ij}=J(P_i,P_j)\) in the ordered Pauli-pair normalization. For each odd-rank cut \(S\), the anti-Pauli inequality \(\ell_S(v)+\ell_S(w)\ge1\) on each anticommuting edge \([v,w]=1\) gives
\[
 J_{ij}\le j J(P_i,S)+i J(P_j,S).
\]
Indeed \(\sum_{w:[v,w]=1}\operatorname{Tr}(P_jW_w)^2
=(D/2)\ell_{P_j}(v)\le Dj/2\). This bounds the two terms after multiplying the edge inequality by the nonnegative trace squares and summing. Thus \(J_{22}\le4J_{2S}\), \(J_{33}\le6J_{3S}\), \(J_{11}\le2J_{1S}\), \(J_{13}\le3J_{1S}+J_{3S}\). Restricting the Pauli anti-projection to \(\Lambda^2\) gives \(\kappa_1\le2J_{22}\), \(\eta\le2J_{33}\). The earlier two-slot polarization gives \(\kappa\le4(J_{13}+\sqrt{J_{11}J_{33}})\), so
\[
 \kappa\le4(\sqrt{3J_{1S}}+\sqrt{J_{3S}})^2,\qquad
 4(h^2J_{1S}+q^2J_{3S})\ge
 \max\left\{q^2\eta/3,\ \frac{g^2\kappa}{h^2+3q^2}\right\}.
\]
The second choice follows by weighted Cauchy–Schwarz; take the quotient as zero at \(h=q=0\). Finally the old anticommuting estimate only used pairs among \(P_1,P_2,P_3\). The disjoint pairs connecting these three cuts to \(P_5,P_7\) carry coefficients \(4(h^2,k^2,q^2)\) times \((b-c)^2,d^2\), respectively. With \(R=k^2[k^2+(h^2+q^2)/2]\) this gives the full-spectrum addition
\[
 2J(C,C)\ \ge\ g^2\kappa+R\kappa_1+
 [(b-c)^2+d^2]\left[\frac{k^2\kappa_1}{2}
 +\max\left\{\frac{q^2\eta}{3},\
            \frac{g^2\kappa}{h^2+3q^2}\right\}\right]. \tag{7}
\]
The maximum allocates the shared \(J_{1S},J_{3S}\) payment once. All of (7) is disjoint from (6) and the exterior compression. [Earlier two-slot estimate and odd-rank inequality](rank7_two_probe_anticommuting.md) · [Shared two-slot polarization](rank7_shared_anchor_twelve_and_anticommuting.md)

## Strict improvement on an actual frame

In a four-qubit computational space choose \(x_2=(|2\rangle+|8\rangle)/\sqrt2\) and \(x_i=|i\rangle\) for the other six labels \(0,\dots,6\). The function \(r\) equals one on XOR direction \(1\), one half on directions \(2,8,3,9\), and zero elsewhere. Each nonzero direction has \(D/2\) odd Pauli labels, so \(\eta=1\). In a coordinate wedge, the added coordinate \(8\) cannot complete a zero-XOR quadruple with three other labels less than eight. Thus all original Fano wedges containing label 2 lose half their weight and the other entries stay the same. Accordingly \(U_\triangle=-[(\alpha+\beta+\gamma)a+bd+cd]/2\).

At \((44,20,15,3/2,5/4,11/10,1)\), all three spectral inequalities \(\gamma d>ab,\ \alpha cd>\beta ab,\ \gamma(a-b)>c(a-d)\) hold strictly. Indeed their respective pairs of values are \(15,15/8\), \(242/5,75/2\), and \(15/4,11/20\). Here \(j_t=1298/5,\ U_\triangle=-2417/40\). Adding \(z=j_t\) in (6) increases the displayed lower bound by at least
\(24j_t U_\triangle+12j_t^2\eta=432234\). The exterior gain of this specific frame is negative.

The standard-library verifier checks each of the 232 possible matchings for the one-price and two-price bounds, using all 28 coefficients of the seven forward spectral gaps. Twelve of the 232 two-price checks need the cone polynomial in (4). The verifier also reconstructs the rotated coordinate exterior weights and its positive mixed payment. [Exact verifier](../verification/verify_rank7_triangle_probe_tail_equalization.py)
