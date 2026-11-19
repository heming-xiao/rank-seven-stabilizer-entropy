# A joint triangle and exterior completion comparison at rank seven

November 18, 2026. For arbitrary ordered positive rank-seven
Schmidt probabilities \((\alpha,\beta,\gamma,a,b,c,d)\), the
triangle defect and the exterior three-head completion deficit
give a common dimension-independent payment. This converts a
physical triangle mixed shift into a scalar test on the six
existing exterior directions, with no additional frame variable.
The test is sufficient for optimality on all qubit cuts over
arbitrary complex local unitaries.

Normalize \(d=1\). Set \(h=\alpha-\beta,k=\beta-\gamma,q=\gamma-a\),
\(p=a-b,X=h+k+q,Y=k+q,L=h+2k+3q,g=hq,\Delta=kX,J=Yq\).
Use \(n=\nu_+\), \(v=(L_{01}-2)_+\), \(P=\max(n,v)\),
\(M=\max(n,v/2)\), \(Z=\max(5n/2,2v,2n+v)\), and
\(S=(2n+v-3M)_+\). Then \(0\le S\le P\le1/2\).
Write \(e=1-w_{0123}\), \(x=1-\sum_{i=3}^6w_{012i}\).
The three-head triangle's defect is \(\eta\).
[Exterior directions and reserve](rank7_uniform_cut_packing.md).

## Eliminating the frame's completion variable

The triangle completion density \(R_\omega\) is positive
with trace one. Any unit vector in the tail four-space can
be taken as the fourth column of the frame without changing
\(n,v\). On this rotated frame \(1-w_{0123}\ge P\). Thus the
largest eigenvalue of the tail compression of \(R_\omega\)
is at most \(1-P\). The largest eigenvalue of \(R_\omega\)
itself is at most \(1-P+x\). Indeed split
\(R_\omega^{1/2}I R_\omega^{1/2}\) into the tail
projection, whose norm equals the compressed norm, and its
complement, whose trace is \(x\). At \(t=(P-x)_+\le1/2\)
the upper bound on the largest eigenvalue gives
\(\operatorname{Tr}R_\omega^2\le(1-t)^2+t^2\) by majorization.
The quantitative concentration bound therefore gives
\[
                      \eta\ge (P-x)_+/40.
\]
The stronger bound \(\eta\ge t(1-t)/20\) is also available.
[Top-four occupancy](rank7_low_head_tail_prices.md) ·
[Completion concentration](rank7_six_mode_shared_probe.md).

Let a nonnegative completion coefficient \(C\) be available,
and suppose the normalized actual triangle payment beyond its
linear mixed term is \(40W\eta\), with \(W\ge0\).
After the base singleton loss \(bcLM\) the geometric increment
and remaining completion terms pay
\[
 C pP+C bx+q(S-x)_++40W\eta
 \ \ge\ C pP+
      \min\{qS+WP,\ CbS+W(P-S),\ CbP\}.
 \tag{1}
\]
Indeed \(D_A\ge pe+bx\) and \(e\ge P\).
The minimum of the resulting piecewise affine function of
\(x\ge0\) occurs at \(0,S,P\). The allocation uses the
\(Cb x\) term once. In particular when \(Cb\ge q+W\), the
available increment is the full earlier \(qS\) and an additional
\(WP\). [Existing geometric increment](rank7_uniform_cut_packing.md).

## A sufficient spectrum test with all three mixed shifts

Put \(A=(101/100)168\),
\(H=b(c-1)\), \(\rho=\min(H,(\gamma-c)p)\),
\(j_s=(\beta-c)(\gamma-b)-\rho\), and
\(G=(g-(200/11)(H-\rho))_+\).
Choose \(s=5G/4,t=5\Delta/4\),
\(\lambda=24s/A,\mu=24t/A\), and define
\[
 C_0=XYq-\lambda(Y+q)-\mu q,\qquad
 j_0=Yq+(a-b)Y+(a-c)q.
\]
Here \(C_0\ge0\) by \(g(Y+q)+\Delta q\le2XYq\).
Set \(z=\min(j_0/13,j_s,A C_0/(48L))\) if \(L>0\), zero otherwise.
Use \(\zeta=24z/A\), \(C=C_0-\zeta L\ge0\), and
\(W=12z(2j_0-13z)/(40A)\).
The shared probe uses the earlier direct matching correction,
so the pure-tail anticommuting sector remains available for
the baseline subtraction of the triangle probe. The third
linear term is the difference \(U_\triangle(C_{\rm spec})-
U_\triangle(B_{\rm tail})=-L D_A\) of the two actual spectral
operators in the same frame. Thus only the \(D_A\)
coefficient changes, and the whole auxiliary triangle exterior
deficit \(B_\triangle\) remains in the signed comparison.
[Direct matching correction](rank7_triangle_probe_tail_equalization.md) ·
[Baseline subtraction](rank7_six_mode_shared_probe.md) ·
[Signed expansion](rank7_three_price_head_expansion.md).

The shared and highest cross coefficient
\(s\Delta+tg-st\ge0\) follows from \(s\le2g,t\le2\Delta\).
The two cross coefficients involving the triangle are
\(s(j_s-z)+zg\) and \(t(j_s-z)+z\Delta\), both nonnegative.
The actual Pauli losses then pay the three linear shifts,
\(40W\eta\) in units of \(A\), and the following additional
prices:
\[
 \begin{aligned}
   A_s &=
     [g^2+12s(2G-s)+((b-c)^2+1)g^2/(h^2+3q^2)]/(12A),\\
   A_1 &=
     [R+12t(2\Delta-t)+((b-c)^2+1)k^2/2]/[(5/2)A],\\
   R&=k^2[k^2+(h^2+q^2)/2].
 \end{aligned}
\]
Their contributions are \(A_sP+A_1v\).
The ratio in \(A_s\) vanishes when \(h=q=0\).
The odd cross-cut reserves in these two prices do not reuse
the pure-tail anticommuting term in the triangle payment.
[Odd-cut reserve and Gram identities](rank7_triangle_probe_tail_equalization.md).

With \(\sigma_1,\sigma_2\) the two true positive amplitude gaps
and \(\omega=(aXYq-\Delta/3)_+/(cg+2aXYq)\), the sufficient
inequality is
\[
\begin{aligned}
 (g-\lambda)cn+(\Delta-\mu)v \ \le\;&bcLM+Z\\
 &+\big[Lp(a-c)(a-1)+p^4+2(g-\lambda)p^2
         +(\Delta-\mu)p(a-c)+3Jp^2+Cp\big]P\\
 &+(\Delta-\mu)(b-1)(c-1)\max(v,n/2)\\
 &+\min\{qS+WP,\ CbS+W(P-S),\ CbP\}\\
 &+A_sP+A_1v+(64v\sigma_1^2+96n\omega\sigma_2^2)/A .
 \tag{2}
\end{aligned}
\]
Take zero for the undefined trace ratio when its denominator is
zero. The other exterior terms follow from the weighted
singleton and prefix losses and the constant deficit.
On each sector delimited by
\((n,v)=(1,0),(1,1/2),(1,1),(1,2),(1,4),(0,1)\), all
expressions apart from the minimum in (2) are affine in
the excesses. Checking (2) amounts to checking the inequality
for all three arguments of the minimum, so the same six
rays suffice. Applied on \(E>0\), the comparison pays \(AE\)
and leaves strictly positive paired margin. Nonpositive gain
again retains the full actual defects.
[Signed and singleton losses](rank7_low_head_tail_prices.md) ·
[Weighted highest-pair prefix](rank7_harmonic_tail_transport.md) ·
[Nested compression](rank7_uniform_cut_packing.md).

The exact example checker uses a fully distinct spectrum whose
old two-shift test, with the same shared and highest shifts,
has a negative margin. With the third shift every ray has
margin greater than \(7/50\). This demonstrates the increase
in the particular comparison and by continuity an open optimal
neighborhood. The example also satisfies the separated-bottom theorem. [Exact example checker](../verification/verify_rank7_triangle_completion_price.py).

