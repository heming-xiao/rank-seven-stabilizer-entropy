# Uniform packing for the three nested leading-edge probes

November 18, 2026. For an ordered positive rank-seven spectrum
\((\alpha,\beta,\gamma,a,b,c,d)\), set
\[
 X=\alpha-a,\qquad Y=\beta-a,\qquad Z=\gamma-a,\qquad
 g=(X-Y)Z,\quad \Delta=X(Y-Z),\quad J=YZ .
\]
Write \(U_1,U,U_\triangle\) for the weighted exterior differences from
the sorted reference for the edge families \(\{01\},\{01,02\},
\{01,02,12\}\). The normalized linear exterior gain is \(E\).
All comparisons below preserve the same physical frame. Fix
\[
 0\le\lambda\le g,\qquad0\le\mu\le\Delta,\qquad 0\le\zeta\le J,\qquad
 C=XYZ-\lambda(Y+Z)-\mu Z-\zeta(X+Y+Z).
 \tag{1}
\]
The next packing price holds throughout this cube, including when \(C\)
is negative.

Let \(v=L_{01}-2,\ \nu=L_{01}+L_{02}-4,\ v_\triangle=L_{01}+L_{02}
+L_{12}-6\le0\). The four-tail values are \(r_i=t_i\), \(i=3,4,5,6\).
Set \(A_i=w_{012i},\ x=1-\sum_i A_i,\ D_A=a-\sum_i r_iA_i\).
For all three single-head totals \(T_i=\sum_{I\ni i}w_I\) and the full
occupancy \(N=\sum_Iw_I\) let \(\delta\) denote actual minus reference.
With \(h=X-Y,\ k=Y-Z,\ q=Z\), the conclusion is
\[
\begin{aligned}
 E-\lambda U-\mu U_1-\zeta U_\triangle
 \le {}&(g-\lambda)cd\,\nu+(\Delta-\mu)d^2v
        +(J-\zeta)d^2 v_\triangle-C D_A+d^4\delta N\\
 &+d^3[h\,\delta T_0+k\,\delta(T_0+T_1)+q\,\delta(T_0+T_1+T_2)] .
\end{aligned}
\tag{2}
\]
The signed \(v_\triangle\) and \(D_A\) terms are retained. This formula
extends the earlier two-price region and allows continuous three-probe
shifts with no spectrum-specific packing LP. [Definitions of the third probe](rank7_triangle_probe_tail_equalization.md)

## Exact expansion about four equal highest probabilities

Keep the four tails fixed and temporarily replace the first three values
by \(a\). Denote probe differences at this tied-four-head spectrum by
superscript \(0\). Let \(B_{\le1}\) be the part of \(E\) of degree zero
or one in the three head increments \(X,Y,Z\). Multiaffinity gives
\[
\begin{aligned}
 E &=B_{\le1}+gU^0+\Delta U_1^0+J U_\triangle^0-XYZ D_A,\\
 U&=U^0-(Y+Z)D_A,\qquad U_1=U_1^0-ZD_A,\qquad
 U_\triangle=U_\triangle^0-(X+Y+Z)D_A .
\end{aligned}
\tag{3}
\]
Indeed the second-order terms have weights \(XY,XZ,YZ\) on the three
edge families \(01,02,12\) separately. The three differences between those
coefficients are \(\Delta,g,J\), giving their nested form. The cubic
term needs all three head labels and hence has tail gain \(-D_A\).
For each leading edge its weighted pair difference depends linearly on
the remaining head value, with coefficient \(-D_A\).

In the original seven nonnegative forward gaps, \(B_{\le1}\) comprises the
terms containing at most one index in \(\{0,1,2\}\). Under the temporary
specialization \(b_3=b_4=b_5=0\), this equals the \(d^4\) and \(d^3\)
terms on the right side of (2), since then every tail has value \(d\).
On restoring \(b_3,b_4,b_5\), all restored quartic monomials in
\(B_{\le1}\) have nonpositive gain coefficient by the ordinary forward
certificates. The five original exceptional monomials all contain at
least two indices in \(\{0,1,2\}\). This proves the asserted upper bound
on \(B_{\le1}\) without imposing any constraint on the three prices.
[Forward coefficient proof](rank7_forward_coefficients_independent.md)

## Six physical rows price the shared and triangle probes

For a tail pair \(i,j\) let \(T_{ij}\) count the three wedges \(uvij\)
with \(\{u,v\}\subset\{0,1,2\}\), and let \(B^{12}_{ij}=w_{12ij}\).
Define
\[
 K_{ij}=1-A_i-A_j-T_{ij}\ge0 .
\]
This is exactly the complement-pair row missing the other two tails,
with equality at the reference. Its sum over the six tail pairs is
\(-v_\triangle\). The computational reference has \(A_3^*=1\) and
\(B_{56}^{12,*}=1\), with zero weight on the other members of
these respective families. Directly summing the six weighted rows gives
the two exact decompositions
\[
\begin{aligned}
 cd\nu-U^0
 ={}&\sum_{i<j}(r_i r_j-cd)(K_{ij}+B^{12}_{ij})
       +[a(a-b)+(a-c)(a-d)]x\\
   &+\sum_i(a-r_i)(2a+r_i-b-c-d)A_i,\\[2mm]
 d^2v_\triangle-U_\triangle^0
 ={}&\sum_{i<j}(r_i r_j-d^2)K_{ij}
       +(3a-b-c-d)D_A+\sum_i r_i(a-r_i)A_i .
\end{aligned}
\tag{4}
\]
All summands are nonnegative. In particular \(r_i r_j\ge cd\) for
distinct tails, and \(2a+r_i\ge b+c+d\). To obtain the first identity,
expand \(U^0=-2aD_A+\sum_{i<j}r_i r_j\,\delta(T_{ij}-B^{12}_{ij})\),
subtract \(cd\nu\), then substitute \(K_{ij}\) and use
\(D_A=ax+\sum_i(a-r_i)A_i\). For the second, expand
\(U_\triangle^0=-3aD_A+\sum_{i<j}r_i r_j\,\delta T_{ij}\) and
substitute the same six rows. The sorted five-tail prefix estimate
gives \(U_1^0\le d^2v\) on the same frame.
[Five-tail prefix packing](rank7_equal_highest_pair_cone.md)

Combining (3) with (4) and the single-pair prefix bound proves (2).
In particular \(U_\triangle\le d^2 v_\triangle\le0\) for every sorted
spectrum: moving from the tied heads to the actual heads further lowers
this probe by \((X+Y+Z)D_A\).

## Compatibility with trace compression and the physical third shift

Let \(n=\nu_+\), \(r=v_+\), \(M=\max(n,r/2)\) and
\(Z_N=\max(5n/2,2r,2n+r)\). If \(C\ge0\), replace \(D_A\) in (2)
by its lower bound \(ax\) and use the geometric rows from the two-price
test. With \(\theta=\min(1,aC/(d^3q))\) for \(q>0\), zero when \(q=0\),
and \(H=3M+\theta(2n+r-3M)_+\), the result is
\[
 E-\lambda U-\mu U_1-\zeta U_\triangle
 \le (g-\lambda)cd\,\nu+(\Delta-\mu)d^2v
       +(J-\zeta)d^2v_\triangle-d^3[(h+2k)M+qH]-d^4 Z_N .
 \tag{5}
\]
The original trace price for the cut containing 0 and either 1 or 2
still applies when \(E>0\). Both the triple deficit and the signed triangle
excess in (2) are available for any sharper joint use. [Geometric prices and uniform cut](rank7_uniform_cut_packing.md)

The special choice \((\lambda,\mu,\zeta)=(g,\Delta,J)/7\) exactly matches
physical shifts \(g,\Delta,J\). The elementary identity
\[
 g(Y+Z)+\Delta Z+J(X+Y+Z)=3XYZ
\]
gives \(C=4XYZ/7\). In particular the full \(H=\max(3M,2n+r)\)
geometric price survives on
\[
                         4aXY\ge7d^3 .
 \tag{6}
\]
If also \(\gamma(a-b)\ge c(a-d)\), the physical tail-matching theorem
has zero additive reference cost and \(G=g\). Its allowed third gap is
\(j_t=(\beta-c)(\gamma-b)-c(b-d)\), which satisfies \(j_t\ge J\):
\[
 j_t-J=(\beta-c)(a-b)+(\gamma-a)(a-c)-c(b-d)\ge0
\]
by \((\gamma-c)(a-b)\ge c(b-d)\). Thus the physical third shift \(J\)
lies in the valid interval \([0,2j_t]\). It delivers an independent term
\(12J(2j_t-J)\eta\) within the simultaneous mixed estimate, while the
matching linear charge \(24J U_\triangle\) is already accounted for
in (5). On (6) none of the six-ray packing prices is reduced by including
this third charge. This is a common spectral region for the three
weighted probes, not a proof of unrestricted rank-seven optimality.
[Three-probe mixed and geometric estimates](rank7_triangle_probe_tail_equalization.md)

The largest available third shift with an unchanged full \(H\) can also
be read off directly. For \(Z>0\), keep \(\lambda=g/7,\mu=\Delta/7\)
and set
\[
 L=\frac{XYZ-(g/7)(Y+Z)-(\Delta/7)Z-d^3 Z/a}{X+Y+Z}.
\]
If \(L\ge0\) and the matching cone holds, every
\(0\le z\le\min(2j_t,7J,7L)\) keeps \(aC\ge d^3q\). Hence the
largest guaranteed coefficient \(12z(2j_t-z)\) on the triangle defect
while maintaining the previous \(H\) occurs at \(z=\min(j_t,7J,7L)\).
This optimization uses the version of (5) that drops the nonpositive
\((J-\zeta)d^2 v_\triangle\); retaining that signed term gives another
explicit tradeoff.

## Sharpness of the signed completion price in a physical frame

Take four equal positive tails \(a=b=c=d\) and permute the computational
frame by exchanging labels 2 and 6. All seven Fano planes remain in the
support, each label still occurs four times, and each pair still occurs
twice. The three highest labels occupy computational points \(0,1,6\);
their unique affine completion is \(7\), outside the rank-seven support.
It follows that \(x=1,\ D_A=d\), while \(\nu,v,v_\triangle,\delta
N,\delta T_i\) all vanish. At the tied-four-head auxiliary spectrum
all seven probabilities then equal \(d\); the auxiliary weighted
differences and \(B_{\le1}\) vanish identically. By (3) the actual value is
\[
 E-\lambda U-\mu U_1-\zeta U_\triangle=-Cd .
\]
Thus the signed completion coefficient in (2) cannot be increased.
Dropping the completion term in a uniform all-frame comparison requires
\(C\ge0\) already on this physical flat-tail family. For common relative
prices \((\lambda,\mu,\zeta)=t(g,\Delta,J)\) this forces \(t\le1/3\)
when \(XYZ>0\). The individual pure exterior gain for this frame is
\(-dXYZ\), so this obstruction concerns the unconditional packing
statement.

The [exact verifier](../verification/verify_rank7_three_price_head_expansion.py) expands
(3), both identities in (4), and the balanced-price identity as sparse
integer polynomials. It checks all 35 wedge columns, the two reference
support statements, and 91 original rational forward duals for the
restored low-degree tail terms, using Python's standard library.

