# A finite comparison for equal fifth and sixth probabilities

November 18, 2026. This is a candidate route to the full rank-seven
family \((\alpha,\beta,\gamma,a,c,c,1)\) with \(d=1\).
The physical implications of the tests below were independently
reviewed. The full interval cover must pass before declaring this
family solved. [Interval checker](../verification/verify_rank7_equal_fifth_sixth.py).

## Unresolved subdomain and exact box contractions

Use \(p=a-c\), \(h=\alpha-\beta\), \(k=\beta-\gamma\),
\(q=\gamma-a\), \(X=h+k+q\), \(Y=k+q\), \(g=hq\), and
\(\Delta=kX\). The earlier global reductions, together with the
new small-shared test, limit the initial comparison to
\[
 (h,k,q,p,c)\in[0,190]\times[0,11/2]\times[1/5,17]\times[0,1]
                         \times[101/100,2].
\]
A spectrum still outstanding after the tail-weighted residual
test must have
\[
 \frac{122}{25}\Delta^2+\max(g^2/24,q^4/72)
                   <144D\Delta,\qquad
       D=1-p^2-(c-1)^2>0 .
\]
This follows by evaluating that test at \(t=\Delta\) and dropping
the nonnegative terms on its payment side, including the paid
completion loss and \(168kc^2\).
Completing the square gives
\(\Delta<(1800/61)D\), \(g<160D\), \(q<17\sqrt D\).
Failure of the small-shared and the pure low-head test requires
\(h>3c/5\), \(q>c/5\), and \(q+2k/c>c\).
The interval checker intersects each box with outward rational
consequences of these inequalities before taking the next
subdivision. [Global domain](rank7_remaining_domain.md) ·
[Small-shared theorem](rank7_small_shared_gain.md) ·
[Weighted residual](rank7_weighted_split_residual.md) ·
[Pure low-head test](rank7_low_head_tail_prices.md).

## Joint price for six exterior directions

Set \(L=h+2k+3q\), \(J=Yq\), \(P=\max(n,v)\),
\(M=\max(n,v/2)\), \(Z_0=\max(5n/2,2v,2n+v)\), where \(n,v\)
are the two positive parts of the exterior excesses.
For mixed shifts \(s,t\), put \(A=(101/100)168\),
\(\lambda=24s/A\), \(\mu=24t/A\), and
\(C=XYq-\lambda(Y+q)-\mu q\).
The shifts below satisfy \(0\le s\le3g/2\),
\(0\le t\le7\Delta/4\), ensuring \(C\ge0\).
The auxiliary-frame deficits satisfy
\[
  B_s\ge2p^2(1-w_{0123}),\quad
  B_1\ge p^2(1-w_{0123})+(c-1)^2\max(v,n/2),\quad
  B_\triangle\ge3p^2(1-w_{0123}).
\]
Use \(1-w_{0123}\ge P\). Together with \(C D_A\), the singleton
and constant deficits provide the following full signed price:
\[
\begin{aligned}
 E-\lambda U-\mu U_1\le{}&
       (g-\lambda)cn+(\Delta-\mu)v-c^2LM-Z_0\\
 &-\big[Lp^2(a-1)+p^4+2(g-\lambda)p^2+
       (\Delta-\mu)p^2+3Jp^2+Cp\big]P\\
 &-(\Delta-\mu)(c-1)^2\max(v,n/2)
          -\min(q,cC)(2n+v-3M)_+ .
\end{aligned}
\]
The \(p^4\) term uses the pure fourth-gap monomial, separate from
the singleton terms. The interpolation of the three-head sum and
\(cCx\) gives the last term. The \(c^2LM\) correction only uses
singleton monomials with a tail-gap index, leaving the original
constant-floor interpolation available. [Signed price](rank7_low_head_tail_prices.md) ·
[Five-tail prefix](rank7_harmonic_tail_transport.md) ·
[Geometric interpolation](rank7_uniform_cut_packing.md).

There are two shared modes. Put \(\epsilon=c-1\),
\(\rho=\min(c\epsilon,(p+q)p)\), \(H=c\epsilon-\rho\),
\(\Psi=\epsilon^2+(h^2+q^2+1)/6\).
The rank-six correction uses \((G,Q)=(g,1+12H^2/(\epsilon^2\Psi))\).
The previous direct uniform correction uses
\((G,Q)=((g-(200/11)H)_+,1)\), where \(G=0\) means zero shared
shift. Both modes allow \(s=uG/Q\), with \(u=3/4,1,5/4,3/2\).
The highest shift uses \(t=w\Delta\), with \(w=1,5/4,3/2,7/4\).
For each chosen common mode and weights, the three-head
anticommuting, disjoint odd-to-leading reserves and mixed square
give coefficients
\[
\begin{aligned}
  A_s&=g^2+\frac{g^2}{h^2+3q^2}
                      +12u(2-u)G^2/Q,\\
  A_1&=R+k^2/2+12w(2-w)\Delta^2 .
\end{aligned}
\]
They pay \(A_s P/12+A_1 v/(5/2)\) in physical units beyond
\(24sU+24tU_1\). The shared-to-highest Gram coefficient is
nonnegative on the allowed shift rectangle. The extra odd
reserve from \(P_7\) and the new \(P_6\) correction use distinct
slots, including the \(P_6,P_7\) pair for the latter.
[Rank-six correction](rank7_six_mode_shared_probe.md) ·
[Joint Gram and odd-slot reserve](rank7_triangle_probe_tail_equalization.md).

The two true nested compression cuts are retained only when
separated, with rational square-root lower bounds. One shift
choice is used for all six directions bounding the pieces
of the homogeneous comparison. Each leaf uses one complete
comparison, and the polynomials or scalar formulas are enclosed
using outward integer arithmetic with a fixed dyadic scale.
An exact successful termination is sufficient for the theorem.
Numerical tests and accepted partial leaves are only evidence
about this certificate route.


## Compiled exact traversal

The running checker is the independently reviewed [C++ implementation](../verification/verify_rank7_equal_fifth_sixth.cpp). It evaluates the same comparisons and contractions with 64-bit endpoints at scale 2^27 and checked 128-bit intermediates. A completion result requires exhaustion of its pending-box stack. The Python implementation is retained as a reference interpreter. [Independent audit](reviews/rank7_fast_interval_and_blossom_independent_review.md).

Build with a C++20 compiler providing signed 128-bit integers, for example `g++ -std=c++20 -O3 verify_rank7_equal_fifth_sixth.cpp -o rank7_interval`. Running the binary with no limit checks the whole domain. A positive numeric argument stops after that many accepted leaves and is a diagnostic.
