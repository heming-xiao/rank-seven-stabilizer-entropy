# Shared and triangle Pauli payments with arbitrary bottom probabilities

November 18, 2026. Let the positive spectrum be proportional to
\((\alpha,\beta,\gamma,a,b,c,d)\) in descending order. Two physical
inequalities remove the sign requirements on the shared and triangle
quadratic payments. They apply also when \(a=b\) and \(c>d\).
The first retains a six-mode matching slack. The second subtracts
the mixed operator with the three highest weights lowered to \(a\).
An allocation in (11) allows simultaneous use on a single frame.

Use \(X=\alpha-a,\ Y=\beta-a,\ Z=\gamma-a\),
\(h=X-Y,\ k=Y-Z,\ q=Z,\ g=hq,\ \Delta=kX\), and
\(j=(\beta-c)(\gamma-b)\). Write \(L=L_-(C)=\mathcal B\Lambda^2 C\).
The shared, highest-pair and triangle probes are \(u,u_1,w\), with
twice their squared norm \(\kappa,\kappa_1,\eta\). Their three off-diagonal
Gram entries, also doubled, are \(c_1,\lambda,\lambda_1\) for
\((u,u_1),(u,w),(u_1,w)\). Their weighted exterior differences from
the computational reference are \(U,U_1,U_\triangle\). All real inner
products below are Hilbert–Schmidt inner products.
[Probe and Pauli normalizations](rank7_triangle_probe_tail_equalization.md)

## A six-mode physical price for the shared probe

Let \(P_i\) project onto the first \(i\) modes, indexed starting at zero.
Put \(z_6=L_-(P_6)\), \(\beta_6=2\|z_6\|^2\) and
\[
 W_6=\sum_{e\in\{01,02\}}\sum_{\substack{I\supset e\\ I\subset\{0,\ldots,5\}}}w_I.
\]
The exact polarization at \(C=P_6\) and the six-mode comparison give
\[
 2\langle u,z_6\rangle=2+W_6-\langle p s_6\rangle,\qquad W_6\le3.       \tag{1}
\]
Here \(p=p_{01}+p_{02}\), \(s_6=\sum_{i<j<6}p_{ij}\).
For the second claim use the matching polytope on complementary pairs
of the six modes. An edge on the three vertices \(3,4,5\) has cost two,
an edge from \(1\) or \(2\) to those three vertices has cost one, and
all other edges have cost zero. At most one edge of cost two fits.
After using it only one edge of cost one fits. Without such an edge
at most two cost-one edges fit. The reference realizes three.
[Six-mode physical matching polytope](rank7_two_low_endpoint_interpolation_independent.md)

Let \(e=c-d,\ \rho=\min\{be,(\gamma-c)(a-b)\}\),
\(K=be-\rho,\ j_s=j-\rho\). Substitute (1) into the existing shared
matching inequality, dropping its nonnegative \(45\) correction. This gives
\[
 2\langle u,L\rangle\ge U+\Delta c_1+g\kappa+j_s\lambda
               +K(3-W_6)+2K\langle u,z_6\rangle .                       \tag{2}
\]
The highest-pair inequality \(2\langle u_1,L\rangle\ge
U_1+\Delta\kappa_1+gc_1+j_s\lambda_1\) holds on the same frame.

Write \(J_{ij}=J(P_i,P_j)\). Restricting the anticommuting Pauli
projection of \(P_6\otimes P_6\) to the antisymmetric copies gives
\(\beta_6\le2J_{66}\). For each odd-rank spectral cut \(P_i\),
\(J_{66}\le12J_{6i}\). Indeed an anticommuting Pauli pair incurs total
leakage at least one on \(P_i\). In the resulting two sums use
\(\sum_{v:[v,v']=1}\operatorname{Tr}(P_6W_v)^2
\le(6D)/2\), in physical dimension \(D\). The coefficients
\(2e^4J_{66},4e^2[h^2J_{16}+q^2J_{36}+(b-c)^2J_{56}+d^2J_{67}]\)
therefore add at least
\[
  e^2\Psi\beta_6,\qquad
  \Psi=e^2+\{h^2+q^2+(b-c)^2+d^2\}/6.                                \tag{3}
\]
All five slots are separate from the previously used leading-cut
slots and the old leading-to-odd-cut reserve.
[Anticommuting slots](rank7_two_probe_anticommuting.md) ·
[Odd-cut reserve](rank7_triangle_probe_tail_equalization.md)

In the mixed square shifted by \(su+tu_1\), the last term of (2)
contributes \(48sK\langle u,z_6\rangle\ge
-24sK\sqrt{\kappa\beta_6}\) for \(s\ge0\). With (3) it costs at most
\(144s^2K^2\kappa/(e^2\Psi)\) by completing the square. Thus the
shared part of the total payment, apart from its nonnegative Gram cross
coefficients for \(s\le g,\ t=\Delta\), includes
\[
 24s[U+K(3-W_6)]+12s[2g-s(1+12K^2/(e^2\Psi))]\kappa .                \tag{4}
\]
When \(e=0\) put the displayed fraction equal to zero, since \(K=0\).
In particular the choice \(s=g/(1+12K^2/(e^2\Psi))\) always has a
strictly positive quadratic price when \(g>0\). At
\((19,9,8,3,3,2,1)\), \(g=50,\ K=3,\ \Psi=133/6\).
The older uniform shared coefficient \(g-(200/11)K\) was negative
and (4) gives \(s=6650/781>0\). This is an improvement of the mixed
comparison at this spectrum, without an assertion about necessity for
its full entropy comparison.

## A triangle price without a completion penalty

Define the single-particle baseline \(B\) on the same eigenvectors
with values \((a,a,a,a,b,c,d)\), zero outside the actual support, and
write \(L_B=L_-(B)\). In the matching bound for \(L-L_B\) the
edge costs are \(t_it_j-B_iB_j\). For the three leading increments
\(y=(X,Y,Z)\), a leading edge \(ij\) costs \(a(y_i+y_j)+y_i y_j\),
a leading-to-tail edge \(is\) costs \(y_i t_s\), and a tail edge costs
zero. The optimum conditioned on leading edge \(ij\) is
\(a(X+Y+Z)+y_i y_j\). Each is reached in its own reference matching
by pairing the remaining head to vertex 3. The optimum with no leading
edge is \(aX+bY+cZ\), by the rearrangement inequality. The three gaps
between successive bounds are \(\Delta,g\), and
\[
                    j_0=YZ+(a-b)Y+(a-c)Z .                              \tag{5}
\]
In particular \(j_0=j\) if \(a=b\). Multiplying the conditional bound
by the triangle mass \(r=p_{01}+p_{02}+p_{12}\) and summing gives
\[
 2\langle w,L-L_B\rangle\ge
 U_\triangle(C)-U_\triangle(B)+\Delta\lambda_1+g\lambda+j_0\eta .       \tag{6}
\]
For example the sum of the three conditional leading optima equals
the direct leading-edge costs plus the reference completion difference
\(a(X+Y+Z)\), giving the stated constant. The physical signed packing
inequality \(U_\triangle(B)\le0\) permits retaining the favorable
term \(-U_\triangle(B)\) or dropping it. On the same frame the
difference in (6) is exactly \(-(X+Y+Z)D_A\).
[Signed triangle packing](rank7_three_price_head_expansion.md)

The anticommuting probability of the baseline obeys
\(J(B,B)\ge\|L_B\|^2\) by restriction to the antisymmetric copies.
The commutator spectral-gap comparison gives
\[
   2J(C,C)\ \ge\ 2J(B,B)+2\sum_{i,j=1}^3d_i^2d_j^2J_{ij}
       +4\sum_{i=1}^3d_i^2J(P_i,B),\qquad (d_1,d_2,d_3)=(h,k,q).       \tag{7}
\]
Indeed on each matrix-element pair the squared probability difference
dominates the squared baseline difference plus the sum of the squared
gap contributions from the three leading cuts. Apply this first on
one Pauli slot of the commutator formula and then on the second.
The last term may then be split on the baseline cuts.
Thus the pure baseline term in (7) is separate from the old leading
and leading-to-tail anticommuting payments.

Using (6) in the mixed square shifted by \(z w\), for \(z\ge0\),
costs at worst
\[
   2J(B,B)+48z\langle w,L_B\rangle\ \ge\ -144z^2\eta .                 \tag{8}
\]
Indeed \(\|w\|^2=\eta/2\). Including the mixed-square term
\(-24z^2\|w\|^2\) therefore gives
\[
  24\|L\|^2+2J(B,B)\ge
  24z[U_\triangle(C)-U_\triangle(B)+\Delta\lambda_1+g\lambda]
                   +12z(2j_0-13z)\eta .                                \tag{9}
\]
In particular \(z=j_0/13\) gives a positive coefficient \(12j_0^2/13\)
whenever \(j_0>0\). Formula (9) applies also outside the earlier tail
cone and at every degeneracy.

## Using one allocation for the two corrections

To combine (2) and (6) spend a fraction \(0\le\theta<1\) of
\(2J(B,B)\) on the pure baseline slots in (3), and the rest on (8).
The \(J_{16},J_{36}\) terms in (7) are still free for (3).
Use
\[
 \Psi_\theta=\theta\{e^2+[(b-c)^2+d^2]/6\}+(h^2+q^2)/6.              \tag{10}
\]
If \(K>0\) and \(s>0\), choose \(\Psi_\theta>0\). If \(sK=0\) the
shared correction is zero. The mixed norm and the allocated anti
slots together pay at least
\[
\begin{aligned}
 &24s[U+K(3-W_6)]+24tU_1+24z[U_\triangle(C)-U_\triangle(B)]\\
 &+12s[2g-s(1+12K^2/(e^2\Psi_\theta))]\kappa
   +12t(2\Delta-t)\kappa_1
   +12z[2j_0-z(1+12/(1-\theta))]\eta\\
 &+24[s\Delta+tg-st]c_1
   +24[sj_s+zg-sz]\lambda+24[tj_s+z\Delta-tz]\lambda_1 .             \tag{11}
\end{aligned}
\]
The three cross terms are nonnegative for \(0\le s\le g,\ t=\Delta,\
z\ge0\). The old head payments and the old leading-to-rank-five and
leading-to-rank-seven payments are independent of (11). Setting
\(\theta=1,z=0\) recovers (4).

## Quantitative completion concentration at a degenerate tail

There is a separate improvement of the triangle's physical completion
density \(R\). In the Pauli ensemble with weights proportional to \(r_b\)
let \(N_b,T_b\) denote the line projectors on its leading kernel and
outside completion. The known relations are
\(\mathbb E N_b=I_3/3,\ \mathbb E T_b=R,\ \mathbb E(1-r_b)=\eta/3\).
The pairwise bound
\((1-\operatorname{Tr}N_bN_c)(1-\operatorname{Tr}T_bT_c)
\le40[(1-r_b)+(1-r_c)]\) holds for every pair of positive-weight labels.
For two independent samples its left expectation equals
\[
 \frac23-\operatorname{Tr}R^2+\operatorname{Tr}\rho^2,\qquad
              \rho=\mathbb E (N_b\otimes T_b).
\]
Since \(\operatorname{Tr}_1\rho=R\), the Hilbert–Schmidt partial-trace
bound gives \(\operatorname{Tr}\rho^2\ge\operatorname{Tr}R^2/3\).
Consequently
\[
                      1-\operatorname{Tr}R^2\le40\eta.                 \tag{12}
\]
For \(a=b\), choose the cheaper completion line \(x_4\) in the
double eigenspace orthogonal to a principal eigenvector of \(R\).
This preserves the spectral operator and the leading probes. Its
completion \(A_4\) is at most \(1-\lambda_{\max}(R)\le40\eta\).
For higher degeneracy the same upper bound holds on the *sum* of
the diagonals on all tied lines except one. This can be used in the
earlier, differently priced triangle polarization.
[Pairwise line inequality](rank7_triangle_quantitative_rigidity.md) ·
[Earlier completion charges](rank7_full_spectrum_triangle_polarization.md)

## A physical obstruction to pricing the disjoint tail terms individually

In dimension 16 take
\[
 x_0=(|0\rangle+|2\rangle)/\sqrt2,\quad
 x_1=(|1\rangle+|4\rangle)/\sqrt2,\quad x_2=|8\rangle,\quad
 x_3=(|0\rangle-|2\rangle)/\sqrt2,\quad
 x_4=(|1\rangle-|4\rangle)/\sqrt2 .
\]
Complete with any two distinct computational basis vectors outside
these five coordinates. For \(u_{34}=\mathcal B P_{x_3\wedge x_4}\),
the exact disjoint-pair polarization gives
\[
 2\langle w,u_{34}\rangle
 =\sum_{i<j\le2}w_{ij34}-\langle r p_{34}\rangle=-\tfrac14 .
\]
Indeed the coordinate terms of the three four-wedges contain no
zero-XOR quadruple. Both \(p_{34}\) and \(p_{01}\) have value \(1/4\)
on the four XOR directions \(1,3,4,6\); each direction has normalized
mass one. The other two leading edges have value \(1/2\) on two
directions each, respectively \(8,10\) and \(9,12\). Thus
\(\eta=3-[4(1/4)^2+4(1/2)^2]=7/4\). When \(a=b\) the five high
eigenvectors of the baseline \(B\) above span a coordinate space,
so \(L_B=0\) at all allowed \(c,d\), even though its \(34\) constituent
has strictly negative triangle polarization. This rules out a
termwise nonnegative baseline proof and any uniform strictly positive
baseline payment proportional to \(\eta\). It leaves the sign of the
*whole* baseline polarization open.

These are lower bounds on the actual physical defects. To establish
optimality for every \(a=b\), a spectral comparison must still show
that those payments and the exterior compression cover the signed
exterior gain for every frame.

The exact verifier checks 76 six-mode and 232 seven-mode matchings, including reference saturation in all four score types. [Exact matching verifier](../verification/verify_rank7_six_mode_shared_probe.py) · [Independent review](reviews/rank7_six_mode_and_middle_gap_independent_review.md).
