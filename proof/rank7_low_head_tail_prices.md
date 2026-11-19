# An unbounded pure-exterior cone and an explicit low-floor collar

November 18, 2026. Let \((\alpha,\beta,\gamma,a,b,c,d)\) be ordered positive
Schmidt probabilities, up to common scaling. The sorted computational
representative maximizes the linear four-exterior overlap on **every
complex seven-mode frame** whenever
\[
 \boxed{\quad \gamma-a+\frac{2d}{c}(\beta-\gamma)\ \le\ b .\quad}
 \tag{1}
\]
In particular the largest probability is unrestricted. This implies
order-two nonlocal stabilizer Rényi optimality over all local unitaries
on every qubit bipartition, and a full relative open neighborhood of
optimality at each positive spectrum in (1). Below we give a stronger
two-inequality region and a separate explicit collar valid at every
rank-six boundary point with fourth probability strictly above the fifth.
Both results allow regimes where the shared and individual
highest-pair amplitude gaps vanish. [Purity reduction](rank7_compression_slack_astra.md) · [Strict transfer](rank7_open_interior_neighborhood.md)

## A uniform strengthened three-probe price

Write \(h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a,\
m=\alpha-a,\ S=h+2k+3q,\ g=hq,\ \Delta=km,\ J=(k+q)q\).
Let \(v=L_{01}-2,\ \nu=L_{01}+L_{02}-4,\ n=\nu_+,\ r=v_+\), and
\(M=\max(n,r/2),\ P=\max(n,r)\). Set \(p=a-b,\ t=b-c,\ e=c-d\).
For the constant and singleton-head part \(B_{\le1}\) of the normalized
linear gain, the complete ordered-tail bound is
\[
 B_{\le1}\ \le\ d^4\delta N
       -S\left[bcd\, M+p(a-c)(a-d)\,P\right],
 \qquad \delta N=N-7\le0 .
 \tag{2}
\]
Here \(B_{\le1}\) is the part of \(E\) of degree at most one in
\((\alpha-a,\beta-a,\gamma-a)\) when the actual four tails remain fixed.
In particular (2) responds to arbitrary unequal tails and does not
depend on the location of any exterior spectral threshold.

For the proof, use nonnegative forward gaps
\(b_0,\ldots,b_6=(h,k,q,p,t,e,d)\). For each singleton head index
\(i=0,1,2\), reserve the monomials with one \(b_i\) and the tail triples
in the following table. The numbers in the middle column multiply
\((i+1)b_i\) and the indicated frame excess. The slope is a lower bound
on the reference coefficient minus the actual coefficient.

| Tail triple | Multiplicity | Excess |
|---|---:|---|
| 456, 466, 556, 666 | 1 | \(M\) |
| 566 | 2 | \(M\) |
| 333, 344, 335, 345 | 1 | \(P\) |
| 334 | 2 | \(P\) |

The first two rows expand \(bcd=(t+e+d)(e+d)d\). The last two expand
\(p(a-c)(a-d)=p(p+t)(p+t+e)\). These two families have disjoint
indices. To certify \(M\), the two rational duals for each cost
prove the indicated multiple of \(\nu\) and of \(v/2\); the old
zero-price certificate permits truncation at zero. For \(P\) use
\(\nu\) and \(v\) with equal slopes. All sixty new duals use only the
original 98 rows. Every other singleton-head monomial and every restored
tail-only monomial is an ordinary nonpositive-gain forward coefficient.
The remaining pure-floor term is \(d^4\delta N\), which proves (2).
[Sixty rational prices](../certificates/rank7/rank7_low_head_tail_prices.json) · [Exact verifier](../verification/verify_rank7_low_head_tail_prices.py)

For clarity this replaces the constant and singleton component in the
general three-price formula **without spending any** of its signed
three-head completion or weighted probe deficits. With
\(0\le\lambda\le g,\ 0\le\mu\le\Delta,\ 0\le\zeta\le J\), write
\(C=m(k+q)q-\lambda(k+2q)-\mu q-\zeta(m+k+2q)\) and
\(D_A=a-\sum_{j=3}^6t_j w_{012j}\). The independent probe deficits at
the tied-four-head auxiliary spectrum are
\[
 B_s=cd\nu-U^0,\quad B_1=d^2v-U_1^0,\quad
 B_\triangle=d^2v_\triangle-U_\triangle^0,\qquad
 v_\triangle=L_{01}+L_{02}+L_{12}-6\le0.
\]
All three are nonnegative and the shared and triangle deficits have
explicit six-row decompositions. The retained simultaneous inequality is
\[
\begin{aligned}
 E-\lambda U-\mu U_1-\zeta U_\triangle
 \le{}& (g-\lambda)(cd\nu-B_s)+(\Delta-\mu)(d^2v-B_1)\\
 & +(J-\zeta)(d^2v_\triangle-B_\triangle)-C D_A+d^4\delta N\\
 &-S[bcd M+p(a-c)(a-d)P].
\end{aligned}
\tag{3}
\]
This includes prices \(C<0\) if the signed term is kept as displayed.
[Exact three-head expansion and probe deficits](rank7_three_price_head_expansion.md)

## Pure exterior optimality without an amplitude cut

For the unadjusted gain \(E\), define
\[
 A=cdg,\quad B=d^2\Delta,\quad
 D_4=(\alpha-b)(\beta-b)(\gamma-b)(a-b),\quad
 Q=D_4+S\,p[(a-c)(a-d)-p^2].
\]
A second all-spectrum packing comparison gives
\[
 E\le A\nu+Bv-Sbcd\,M-QP .
 \tag{4}
\]
To derive it, start directly from the full forward quartic estimate
\(E\le A\nu+Bv\). In the ordinary, nonexceptional part keep the
coupons of (2). In addition all quartics whose indices are at most 3
can only occur on \(0123\) and contribute precisely
\(-D_4(1-w_{0123})\). Their overlap with (2) is exactly the
three monomials \(b_i p^3,\ i=0,1,2\). Remove the duplicated
\(-S p^3P\) from the earlier coupon and use
\[
                    1-w_{0123}\ge P .
 \tag{5}
\]
For the highest pair, add the two triple-completion rows on \(012,013\)
and the complement-pair row on \(23\). Their cost covers \(w_{0123}+L_{01}\)
and their capacities sum to three. For the shared pair, add the directed
row containing 0 and missing 3 to the three complement-pair rows on
\(45,46,56\). They cover \(w_{0123}+L_{01}+L_{02}\) at total capacity five.
Both statements hold column by column; \(w_{0123}\le1\) is itself physical.
These prove (5) and then (4). Equation (4) is a separate unweighted
comparison; its \(D_4\) row is not added to the signed three-price
formula (3).

A sufficient spectrum-only test for \(E\le0\) on all frames is
\[
 \boxed{A+B\le Sbcd+Q,\qquad A+2B\le Sbcd+2Q.}
 \tag{6}
\]
Indeed these conditions cover the two rays \(r=n\) and \(r=2n\) of
\(A n+B r\le Sbcd\max(n,r/2)+Q\max(n,r)\).
On \(r\le n\) the hardest case is \(r=n\). On \(r\ge2n\), fixing \(r\)
gives the hardest case at \(n=r/2\). Linear interpolation in the
remaining sector completes the proof, including the axes.

For the simpler condition (1), keep only the first term \(SbcdM\).
Since \(n\le M\) and \(r\le2M\), the gain paid per \(cdM\) is at most
\[
  h[q+2(d/c)k]+2(d/c)k(k+q).
\]
The first term is at most \(hb\) by (1). Also \(2(d/c)k\le b\), so
the second is at most \(b(k+q)\le b(2k+3q)\). This proves (1) without
any constraint on \(\alpha\).

For the low-floor collar, fix the first six entries with \(a>b\).
Then \(D_4>0\) and the single inequality
\[
              cdg+d^2\Delta\le D_4
 \tag{7}
\]
already implies (6). Equivalently \(d\) may range from zero up to
the lesser of \(c\) and
\(2D_4/[cg+\sqrt{c^2g^2+4\Delta D_4}]\), with no further cap
when both \(g\) and \(\Delta\) vanish. This is a pure-exterior
collar and uses no mixed or actual compression payment.
A direct proof of (7) is to retain only the top-four product loss
in the original quartic certificate and use (5).

## A full-dimensional unbounded no-gap region

For example take arbitrary real unnormalized probabilities satisfying
\[
\begin{gathered}
 \alpha\ge20,\quad 7\le\beta\le8,\quad
 3.9\le\gamma\le4.1,\quad2.9\le a\le3.1,\\
 1.9\le b\le2.1,\quad1.4\le c\le1.6,\quad0<d\le0.1 .
\end{gathered}
\]
Throughout this seven-parameter box the left side of (1) is at most
\(25/14<19/10\le b\). Both familiar positive amplitude cuts fail:
\(\gamma d<ab\) for the shared cut and \(\beta cd<\gamma ab\) for
the highest-pair cut. Also \(\alpha>3b\) and
\(1/a>1/\alpha+1/\beta\), so neither of the earlier elementary pure
exterior cones applies. The open interior projects to a full-dimensional
subset of the normalized rank-seven simplex. The ratio \(\alpha/d\)
has no finite upper bound. As a second example, \((22,8,7,3,2,1.5,0.1)\)
has \(q>b\), so (1) fails, whereas (7) holds with
\(A+B=859/100<600=D_4\).

Whenever \(E\le0\), every actual nonnegative single-frame defect
remains available. The single-frame comparison, independent local-frame
Cauchy–Schwarz transfer, and stabilizer padding give the stated entropy
optimality. At every fixed positive spectrum of (6) the strict
defect-margin transfer supplies an unrestricted relative open neighborhood.
[Prior elementary cones](rank7_unbounded_spread.md) · [Single-frame and neighborhood argument](rank7_open_interior_neighborhood.md)

