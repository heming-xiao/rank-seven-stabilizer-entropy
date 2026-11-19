# Rank-seven optimality for a third-to-fourth gap up to two thirds of the floor

November 18, 2026. For every ordered positive rank-seven Schmidt
spectrum proportional to \((\alpha,\beta,\gamma,a,b,c,d)\), the sorted
computational representative globally minimizes the order-two nonlocal
stabilizer Rényi entropy over arbitrary complex local unitaries on
every qubit bipartition whenever
\[
                             \gamma-a\le 2d/3. \tag{1}
\]
There are no conditions on the other weight ratios, and the endpoint
is included. Each paired comparison retains at least \(1/101\) of the
actual defect. The equality classification and unrestricted relative
open neighborhoods hold throughout the region. In particular (1)
covers the entire low-gap case left by the conditional
[fourth-gap ray transfer](rank7_true_cut_gap_ray.md).
[Paired reduction and equality](rank7_all_tie_equalities.md)

We first treat \(q=\gamma-a\le3d/5\) throughout the next four sections,
then complete the additional strip through \(2d/3\) in the final section.

## Two exterior upper bounds with a common fourth-gap term

Normalize \(d=1\) and put \(h=\alpha-\beta,\ k=\beta-\gamma,\
q=\gamma-a,\ p=a-b,\ X=h+k+q,\ Y=k+q,\ \Delta=kX,\ g=hq\).
Write \(B=h+3q,\ L=B+2k,\ P=p(p+q)\). The shared and highest
positive trace excesses are \(n,v\) and \(M=\max(n,v/2)\).
Take \(A=(101/100)168,\ t=5\Delta/4,\ \mu=24t/A,\ \rho=1-30/A\)
with zero shared and triangle shifts. The actual-frame exterior gain
\(E\) and highest weighted gain \(U_1\) satisfy
\[
\begin{aligned}
 E-\mu U_1&\le cgn+\rho\Delta(1-P)v-bcLM-2v,\\
 E-\mu U_1&\le cHn+\rho\Delta(1-P)v-kbc\,v,\qquad
                   H=g-bB-(5/2)b^2 . \tag{2}
\end{aligned}
\]
The first inequality is the signed exterior expansion. The completion
coefficient is \(C=q(XY-\mu)\ge\rho\Delta q\), and
\(D_A\ge p(1-w_{0123})\ge pv\). The highest tied-four-head deficit
additionally obeys \(B_1\ge p^2v\). Their disjoint prices yield
\(\rho\Delta(pq+p^2)v\). The constant and singleton-head terms give
\(2v+bcLM\). For the second inequality compare to the same frame
with its upper two weights lowered by \(k\). There
\(E_0\le cHn\), using the forward bound when the raw shared excess
is nonpositive. The split gives \(E\le E_0+\Delta U_1-kbc\,v\).
The actual highest weighted difference satisfies
\(U_1\le v-B_1-qD_A\le(1-P)v\) for either sign of the raw highest
excess. This proves (2), including \(\Delta=0\).
[Signed packing](rank7_low_head_tail_prices.md) ·
[Weighted frame split](rank7_weighted_split_residual.md) ·
[Tied-middle comparison](rank7_equal_middle.md)

Since \(g\le(3/5)B\), \(H<0\). Take the first line of (2) with
weight \(\theta=1-g/(bB+5b^2/2)\) and the second with \(1-\theta\).
Their \(n\) terms cancel. Using \(M\ge v/2\) gives
\[
 E-\mu U_1\le
 [\rho\Delta(1-P)-kbc-\theta(bcB/2+2)]v .                    \tag{3}
\]
This bound keeps the same fourth-gap price in both exterior inputs.
It has used no mixed square, anticommuting payment or compression cut.

## The highest physical payment and one scalar comparison

The highest mixed shift supplies \(24tU_1+(45/4)\Delta^2\kappa_1\).
The independent highest anticommuting slots supply \(R\kappa_1\),
where \(R=k^2[k^2+(h^2+q^2)/2]\ge\Delta^2/5\).
Together with \(\kappa_1\ge v/(5/2)\) these give the price
\(J\Delta^2v\) beyond \(\mu U_1\), in units divided by \(A\), where
\[
             J=\frac{45/4+1/5}{(5/2)A}.
\]
This already proves \(D\ge AE\) at \(v=0\) for the total actual defect
\(D\). At \(v>0\), if the actual highest cut separates it pays
\(64\alpha[\sqrt{\beta c}-\sqrt{\gamma ab}]_+^2 v\) in physical
units. This uses \(v\le1/3\) and \(\phi(2+v)\ge(2/3)v\).
[Highest physical shift](rank7_two_probe_separation_and_tail_region.md) ·
[Highest cut and trace](rank7_near_third_fourth.md)

The signed price in (3) increases with \(c\), and so does the
highest squared width. In lower-bounding the available price we may
replace \(c\) by one. We may also use the smaller nonnegative factor
\(\theta_0=1-g/(B+5/2)\ge2/5\).
Define
\[
 {\cal B}=kb+\theta_0(bB/2+2)+\rho\Delta[P-1]+J\Delta^2 .
\]
By (3), either \({\cal B}\ge0\) or the following two inequalities
are sufficient:
\[
 \beta-\gamma ab\ge0,\qquad
   (\beta+\gamma ab){\cal B}+
                \frac{32}{A}\alpha(\beta-\gamma ab)^2\ge0 .   \tag{4}
\]
For the latter use
\((\sqrt u-\sqrt v)^2\ge(u-v)^2/[2(u+v)]\) when \(u\ge v\).

## Analytic exterior of the five-dimensional box

Completing the square gives
\(\rho\Delta-J\Delta^2\le\rho^2/(4J)<32/5\). Also
\(L/2\ge\sqrt\Delta\), since \(L/2\ge(h+2k+q)/2\) and
\((h+2k+q)^2/4-k(h+k+q)=(h+q)^2/4\).

* If \(b\ge3\), use the actual \(\theta\ge4/5\). Then
  \(kbc+\theta bcB/2\ge(12/5)\sqrt\Delta\), and \(2\theta\ge8/5\).
  These sum to at least \(32/5\) when \(\Delta\ge4\).
  When \(\Delta\le4\), \(\rho\Delta\le2\sqrt\Delta\).
* If \(p\ge2/3,\ q\ge3/10\), then \(1-P\le16/45\).
  The maximum of \((16/45)\rho\Delta-J\Delta^2\) is less than
  \(4/5\le2\theta_0\).
  If \(p\ge2/3,\ q\le3/10\), then \(1-P\le5/9\),
  \(\theta_0\ge7/10\), and the corresponding maximum is below
  \(21/10\). For \(\Delta\ge1\) the singleton and constant terms pay
  at least \((7/10)\sqrt\Delta+7/5\ge21/10\).
  For \(\Delta\le1\), \((5/9)\rho\Delta<7/5\).
* If \(h+5k\ge28\), then
  \(kb+\theta_0(bB/2+2)\ge k+B/5+4/5\ge32/5\).

Each analytic comparison proves the strengthened target \(D\ge AE\).

## Exact certificate on the remaining box

Rescale five independent unit variables to
\[
 (h,k,q,p,b-1)=(28u_0,(28/5)u_1,(3/5)u_2,(2/3)u_3,2u_4).
\]
Clear the positive denominator \(B+5/2\) in \({\cal B}\) and (4).
The [exact checker](../verification/verify_rank7_low_third_gap.py) reconstructs
all three rational polynomials and verifies the entire box using
integer Bernstein subdivision. Its tree has **411** leaves for
\({\cal B}\), **201** leaves proving both conditions of (4), and
**6** leaves on which \(h+5k\ge28\). The maximum depth is **25**.
No trial spectrum or floating-point decision enters the certificate.
This completes the first region with the asserted uniform margin.

## Extending through the five-fourths-shift transfer threshold

For \(3/5\le q\le2/3\) let \(s_0=101/100\). The existing
[bottom-pair theorem](rank7_near_two_tails.md) gives the full margin
for \(c\le s_0\), so take \(b\ge c\ge s_0\).
Both inequalities (2) and the cancellation (3) remain valid because
\(g\le(2/3)B\). In (3) replace \(c\) by \(s_0\) and \(\theta\) by
\(\theta_*=1-g/(s_0B+5s_0^2/2)\). Use the complete \(R\) instead
of \(\Delta^2/5\), and retain the separate shared anticommuting
payment \(g^2\kappa\ge g^2v/12\). Thus the new base expression is
\[
 kbs_0+\theta_*(bs_0 B/2+2)+\rho\Delta(P-1)
       +\frac{(45/4)\Delta^2+R}{(5/2)A}+\frac{g^2}{12A}.
\]
In (4) replace both occurrences of \(\beta\) by \(s_0\beta\).
These modifications use no shared mixed shift.

For \(b\ge3\) use the original \(\theta\ge7/9\), giving at least
\((7/3)\sqrt\Delta+14/9\) beyond the quadratic terms.
For \(\Delta\ge5\) this exceeds \(32/5\); for \(\Delta\le5\),
\((7/3)\sqrt{\Delta}\ge\rho\Delta\).
For \(p\ge2/3\) one has \(1-P\le7/45\) and the maximum quadratic
debit is below \(2/3\le2\theta_*\).
Finally \(h+6k\ge36\) already pays \(6+2/3\) since \(\theta_*\ge1/3\).

The additional unit-box coordinates are
\[
 (h,k,q-3/5,p,b-s_0)
       =(36u_0,6u_1,u_2/15,2u_3/3,(199/100)u_4).
\]
The second exact tree has **962** base leaves, **511** true highest-cut
leaves and **12** analytic leaves, with maximum depth **25**.
This proves (1) with the same uniform paired margin.
