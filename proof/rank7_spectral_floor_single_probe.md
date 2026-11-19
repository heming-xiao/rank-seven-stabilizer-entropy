# A spectral floor correction for the highest-pair mixed probe

November 18, 2026. Write the sorted positive Schmidt probabilities as \((\alpha,\beta,\gamma,a,b,c,d)\), with arbitrary overall scale. Put
\[
 h=\alpha-\beta,\quad k=\beta-\gamma,\quad q=\gamma-a,\quad
 g=hq,\quad \Delta=k(\alpha-a),\quad
 H=g-b(h+3q)-5b^2/2,\quad R=k^2[k^2+(h^2+q^2)/2].
\]
Here \(d\) is the smallest probability. The following explicit two-interval family satisfies computational-basis optimality on every qubit bipartition:
\[
 \boxed{\quad
  7hq\le b(h+3q)+5b^2/2,\qquad
  \Delta/d^2\in [0,5]\cup[20,\infty).
 \quad} \tag{1}
\]
The more precise polynomial criterion (4) below also certifies the strictly ordered spectrum \((79/10,19/5,17/10,7/5,13/10,11/10,1)\) and an open neighborhood. The proof uses the actual mixed sector and anticommuting term. It leaves the four-wedge compression defect available.

## Eleven floor coefficients valid on one common physical frame

Let \(E\) be the normalized exterior linear gain of the frame over the sorted representative. Write \(v=L_{01}-2\), \(\nu=L_{01}+L_{02}-4\), \(Y=W_1-(\gamma a+bc)\), in the [conditional matching notation](rank7_general_two_probe_matching.md). Define
\[
 F=d^2\left[\Delta-(h/2+k)(b+c-d)
             -d\{3q/2+2(a+b+c-2d)\}\right],\qquad P=kbcd .
\]
Every frame satisfies the signed order-four bound
\[
                    E\ \le\ Fv+gcd\,\nu. \tag{2}
\]
To prove it use forward gaps \(z=(h,k,q,a-b,b-c,c-d,d)\). In each of the 210 degree-four monomials, the cost vector has 35 four-wedge entries. For \(0166,1166,1266\) the existing certificate charges \(v\); for \(0256,0266\) it charges \(\nu\). These positive charges sum to \(d^2\Delta v+gcd\,\nu\). Instead of discarding the other coefficient losses, the following eleven monomials can each contribute \(-\rho v\):

| Monomial | 0666 | 1666 | 2666 | 3666 | 4666 | 5666 | 6666 | 0466 | 0566 | 1466 | 1566 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| \(\rho\) | \(1/2\) | 1 | \(3/2\) | 2 | 4 | 6 | 2 | \(1/2\) | 1 | 1 | 2 |

For each designated monomial \(M\), the certificate exhibits nonnegative rational prices on the original 98 physical rows which dominate \(\mathrm{cost}_M+\rho\,\mathbf1_{01\subseteq A}\) in all 35 columns and attain exact equality on the reference in total. Thus the signed inequality is valid even for negative \(v\). The remaining 194 ordinary and five exceptional coefficients retain their former duals. Summing the eleven terms gives
\[
 d^3(h/2+k+3q/2+2(a+b+c-2d))
  +d^2(h/2+k)(b+c-2d),
\]
which subtracts from \(d^2\Delta\) to give \(F\). The exact verifier includes all eleven rational duals and checks all \(210\cdot35\) inequalities and 210 reference values using standard-library rational arithmetic. [Floor-price verifier](../verification/verify_rank7_spectral_floor_single_probe.py) · [Forward monomial reduction](rank7_forward_coefficients_independent.md)

## Cancel the shared excess while preserving the signed highest-pair term

Suppose \(H<0\). Then the tied-middle base frame has \(E_0\le0\) in both signs of \(\nu\). For \(\nu>0\) the stronger bound \(E_0\le cdH\nu\) holds. The highest-pair increment satisfies \(E-E_0\le\Delta Y-Pv_+\), and \(Y\le d^2v\). Consequently \(E>0\) forces \(\Delta>0\), \(Y>0\), and \(v>0\). [Tied-middle exterior comparison](rank7_equal_middle.md) · [Highest-pair increment](rank7_highest_pair_split_loss.md) · [Highest-pair weighted prefix](rank7_leading_split_packing.md)

Let \(\theta_0=g/(g-H)\). For any \(\theta_0\le\theta\le1\), combine (2), with weight \(1-\theta\), and the preceding highest-pair increment plus its tied-middle endpoint, with weight \(\theta\). For \(\nu>0\) the remaining shared coefficient is \(cd[(1-\theta)g+\theta H]\le0\). For \(\nu\le0\) use the corresponding nonpositive shared term from (2) and \(E_0\le0\). Thus on every potentially positive-gain frame,
\[
 E\le[(1-\theta)F-\theta P]v+\theta\Delta Y. \tag{3}
\]
Let \(K=5/2\), so \(v\le K\kappa_1\). The conditioned single-probe inequality gives \(2\langle u_1,L_-(C)\rangle\ge \Delta\kappa_1+Y\). For every \(t\ge0\), expanding \(\|L_-(C)-t u_1\|^2\) gives the actual mixed payment \(24tY+12(2t\Delta-t^2)\kappa_1\). The disjoint anticommuting defect pays an additional \(R\kappa_1\). We may therefore choose \(\theta_0\le\theta\le1,\ t\ge0\), with \(12(2t\Delta-t^2)+R\ge0\), to test
\[
 \boxed{\quad
 \frac{12(2t\Delta-t^2)+R}{K}
 \ \ge\ 168[(1-\theta)F-\theta P]
          +(168\theta\Delta-24t)_+d^2.
 \quad} \tag{4}
\]
Here \(0<Y\le d^2v\) justifies the positive-part coefficient. Equation (4) suffices because the normalized exterior gain costs \(168E\). Every strict certificate for a strictly ordered spectrum gives an open neighborhood by continuity if \(\theta>\theta_0\), or by taking \(\theta=\max(\theta_{\rm fixed},\theta_0)\) continuously. More generally the strict difference is a fixed positive price times \(v\), and \(E\le\Delta d^2v\) bounds the gain on the positive branch. This reserves a fixed part of the actual defect for the [open-neighborhood transfer](rank7_open_interior_neighborhood.md). The single-frame comparison passes to independent local unitaries and arbitrary qubit cuts by the standard paired argument and stabilizer padding. [Single-probe geometry](rank7_highest_pair_geometry_five_halves.md) · [Anticommuting comparison](rank7_two_probe_anticommuting.md)

For fixed \(\theta\), (4) does not require a continuous optimization. Without the nonnegative-payment restriction, the best \(t\) is
\[
 t_0=\max\{\Delta,\ \min(7\theta\Delta,\ \Delta+Kd^2)\}.
\]
This follows by differentiating the two concave quadratics on the respective sides of \(t=7\theta\Delta\). The feasible positive interval additionally requires \(t\le\Delta+\sqrt{\Delta^2+R/12}\), so take \(t=\min\{t_0,\Delta+\sqrt{\Delta^2+R/12}\}\).

## A two-interval family and the strictly ordered test spectrum

Under the first inequality in (1) one has \(H<0\) and \(\theta_0\le1/7\). Take \(\theta=1/7\) and \(t=\Delta\); then the term in \(Y\) cancels. With \(x=\Delta/d^2\), \(b+c-d\ge d\), \(a+b+c-2d\ge d\), and \(h/2+k+3q/2\ge\sqrt{k(h+k+q)}\), we obtain
\[
 F\le d^4(x-\sqrt x-2),\qquad R\ge\Delta^2/5.
\]
For \(x>0\) it suffices to check \(61x^2-1800(x-\sqrt{x}-2)>0\). On \(0<x\le4\), the subtracted bracket is nonpositive. On \([4,5]\) the derivative is at most \(610-1800+450<0\), and the value at five is positive by \(\sqrt5>11/5\). On \([20,\infty)\) the derivative is positive, and its value at 20 is \(-8000+3600\sqrt5>0\). When \(\Delta=0\), the endpoint already gives \(E\le0\). This proves (1).

There is also a tail condition covering every value of \(\Delta\). More precisely,
\[
 \boxed{\quad
 7hq\le b(h+3q)+5b^2/2,\qquad a+b+c\ge4d
 \quad} \tag{5}
\]
suffices. Here \(2(a+b+c-2d)\ge4d\), so the bound becomes \(F/d^4\le x-\sqrt{x}-4\). To see that \(x-\sqrt x-61x^2/1800<4\) on all of \(x\ge0\), split at 9 and 16. For \(x\le9\), use \(\sqrt{x}\ge x/3\); the resulting quadratic increases up to 9 on this interval and its endpoint value is \(6-4941/1800<4\). For \(9\le x\le16\), concavity gives \(\sqrt{x}\ge(x+12)/7\); the resulting quadratic is at most \(16200/2989-12/7<4\). For \(x\ge16\), use \(\sqrt x\ge4\) and \(x-61x^2/1800\le450/61<8\). This proves strict payment at all \(x>0\).

For the specified spectrum we have exactly
\[
 g=123/100,\quad H=-1899/200,\quad \theta_0=82/715<1/7,\quad
 \Delta=273/20,\quad R=283563/5000,\quad P=3003/1000 .
\]
Here \(x=13.65\) is between the two intervals of (1). The full polynomial has \(F=379/100\). With \(\theta=1/7,\ t=\Delta\), the effective exterior price in (3), after the \(Y\) term is paid, is \((6F-P)/7=19737/7000\). The exact positive difference between the two sides of (4) is \(5541813/12500\). Even retaining only the first seven floor prices gives \(F=109/20\) and positive difference \(2553813/12500\). None of these comparisons uses four-wedge compression or a pointwise optimization over physical frames.
