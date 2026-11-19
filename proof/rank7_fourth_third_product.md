# A fourth-gap product that pays both leading rank-seven excesses

November 18, 2026. For every ordered positive rank-seven Schmidt
spectrum proportional to \((\alpha,\beta,\gamma,a,b,c,d)\), the sorted
computational representative globally minimizes order-two nonlocal
stabilizer Rényi entropy on every qubit bipartition whenever
\[
                 \boxed{(a-b)(\gamma-b)\ge (2/5)d^2.} \tag{1}
\]
All other spectral ratios are unrestricted. The condition includes
the endpoint. Every spectrum in this region has a positive paired
defect margin and a full relative open rank-seven neighborhood of
optimality. The optimizers are the local Clifford images of the sorted
representative up to phase. [Equality and neighborhood transfer](rank7_all_tie_equalities.md)

Set \(d=1\), write \(p=a-b,\ q=\gamma-a,\ k=\beta-\gamma,\
h=\alpha-\beta\), and let \(X=h+k+q,\ Y=k+q,\ L=h+2k+3q,\
g=hq,\ \Delta=kX,\ Z=p(p+q),\ z=2/5\). By the two existing
theorems it suffices to treat \(1\le c\le9/5,\ c\le b\le3\).
[Large fifth probability](rank7_large_fifth_probability.md) ·
[Separated bottom pair](rank7_separated_bottom_pair.md)

## A simultaneous use of the top-four completion deficit

Put \(A=(101/100)168,\ r=24/A,\ \rho=1-r,\ K=5/2,\
J=(12+1/5)/(KA),\ T=13/(12A)\).
The shared and highest positive excesses are \(n,v\), with
\(P=\max(n,v)\), \(M=\max(n,v/2)\). Thus \(e=1-w_{0123}\ge P\),
the triple-completion deficit has \(D_A\ge pe\), and the tied-four-head
auxiliary deficits obey \(B_s\ge2p^2e,\ B_1\ge p^2e\).
Let \(U,U_1\) be the two actual weighted gains and \(E\) the normalized
exterior gain. For prices \(\lambda,\mu\) and zero triangle price,
the cubic term in \(E-\lambda U-\mu U_1\) is \(-C D_A\), with
\[
  C=qXY-\lambda(Y+q)-\mu q,\qquad XY=g+\Delta+Yq .
\]
On the same frame its singleton and pure-floor terms pay
\(bcLM+2v\), and the signed pair terms pay
\((g-\lambda)B_s+(\Delta-\mu)B_1\) in addition.
[Signed expansion](rank7_three_price_head_expansion.md) ·
[Weighted singleton and top-four price](rank7_low_head_tail_prices.md) ·
[Pure-floor trace](rank7_uniform_cut_packing.md)

Use the highest shift \(t=\Delta\), hence \(\mu=r\Delta\).
For zero shared shift the completion price is exactly
\(q(g+\rho\Delta+Yq)\). For shared shift \(s=g\) and \(\lambda=rg\)
it is at least \(q[(1-2r)(g+\Delta)+Yq]\): the difference is
\(rkqY\). Since the same \(P\) dominates \(n\) and \(v\), the
summands of \(pC P\) proportional to \(g\) and \(\Delta\) can
be used respectively for the two different excesses. Adding the
distinct auxiliary costs on \(p^2 e\) gives, whenever \(Z\ge z\),
\[
\begin{aligned}
 E-r\Delta U_1
 &\le (c-z)g n+\rho(1-z)\Delta v-bcLM-2v,\\
 E-rg U-r\Delta U_1
 &\le [(1-r)c-(1-2r)z]g n+
       [1-r-(1-2r)z]\Delta v-bcLM-2v. \tag{2}
\end{aligned}
\]
For example the zero-shared-shift debit includes
\((2p^2+pq)gn+\rho(p^2+pq)\Delta v\).
In the second line the auxiliary rates \(2(1-r)\) and \(1-r\)
both exceed \(1-2r\). All terms dropped from the negative completion
and triangle prices have the indicated signs. These inequalities
use the actual frame at the given spectrum and do not require the
tied-middle coefficient \(H\) to be negative.

## The highest shift forces a large shared gain on the remaining frames

Write \(D\) for the total physical paired defect. The highest mixed
square supplies \(24\Delta U_1+12\Delta^2\kappa_1\), and the
independent highest anticommuting slots give
\(R\kappa_1\), with \(R\ge\Delta^2/5,\ \kappa_1\ge v/K\).
After division by \(A\) this leaves \(J\Delta^2v\) beyond the linear
charge in the first line of (2). For \(u_0=\rho(1-z)\) and all
\(\Delta\ge0\),
\[
 u_0\Delta-J\Delta^2\le2+\sqrt{\Delta}/9.
\]
For \(\Delta\le9\) use \(\sqrt{\Delta}\ge\Delta/3\) and
\((u_0-1/27)^2/(4J)<2\); for \(\Delta\ge9\) use
\(u_0^2/(4J)<2+1/3\).
As \(L\ge2\sqrt{\Delta}\), the pure floor and \(bcLM/9\) suffice
for this highest residual. The other \(8bcLM/9\) pays the shared
term if \((c-z)g\le(8/9)bcL\). This establishes \(D\ge AE\) there.
[Highest geometry and physical slots](rank7_compact_remaining_spectra.md)

In the remaining spectral regime \(L\ge2\sqrt{3g}\) forces
\[
 g>12(8/9)^2\frac{b^2c^2}{(c-z)^2}
        \ge g_0:=192(8/9)^2z^2=\frac{16384}{675}. \tag{3}
\]
The second inequality uses \(b\ge c\) and
\(c^2/(c-z)\ge4z\), equivalent to \((c-2z)^2\ge0\).

## Joint physical payment independent of the two trace excesses

Use \(s=g,\ t=\Delta\) on spectra satisfying (3)'s first inequality.
The actual shared matching correction is bounded by
\(\tau=(200/11)b(c-1)\), giving shared linear bound
\(2\langle u,L_-(C_{\rm spec})\rangle\ge U+(g-\tau)\kappa+\Delta c_1\).
The simultaneous mixed shift leaves nonnegative cross price and,
after adding the independent \(g^2\kappa\), pays
\((13g^2-24g\tau)\kappa\) beyond the two linear charges.
The highest slots are the same as in the first strategy. The two
strategies are alternative paired comparisons.
[Conditional shared matching correction](rank7_joint_single_cut_regression.md) ·
[Joint shifts](rank7_two_probe_separation_and_tail_region.md)

By (3) and \(b\ge c\),
\[
 \frac{\tau}{g}<
 \frac{200/11}{12(8/9)^2}
   (1-1/c)(1-z/c)^2 \le\frac{1225}{2376}<13/24
\]
when \(\tau>0\), with zero ratio if \(\tau=0\).
The maximum on the right is attained at \(c=9/5\).
Thus the remaining shared coefficient is positive and
\(\kappa\ge P/12\) applies without reversing the comparison.
For \(u_1=1-r-(1-2r)z\), the highest residual
\(u_1\Delta-J\Delta^2\) is at most \(u_1^2/(4J)\).
Its excess above \(2\), times \(v\), is bounded by \(bcLM/8\);
indeed \(v\le2M\) and
\[
  2\big[u_1^2/(4J)-2\big]
      <\sqrt{12g_0}/8<bcL/8 .
\]
It remains to pay the shared residual with \(7bcLM/8\) and the
shared quadratic term. Since \(M,P\ge n\), put
\[
  C_b=(1-r)c-(1-2r)z+K_0 b(c-1),\qquad K_0=400/(11A).
\]
It suffices that \(C_b g-Tg^2\le(7/8)bc\,2\sqrt{3g}\).
Maximizing \(C_b y-Ty^3\) over \(y=\sqrt g\ge0\) reduces this to
\[
                  C_b^3\le81T(7/8)^2b^2c^2 . \tag{4}
\]
For fixed \(c\), \(C_b^3/b^2\) decreases on \(c\le b\le3\).
The sign of its derivative is that of
\(K_0 b(c-1)-2[(1-r)c-(1-2r)z]\), negative even on replacing
the first term by \(3K_0(9/5-1)\) and \(c\) in the second by one.
Set \(b=c\). The derivative of \(C_c/c^{4/3}\) has the sign of
\[
            2K_0c^2-(1-r-K_0)c+4(1-2r)z ,
\]
which is positive by its negative discriminant. At \(c=9/5\) direct
rational substitution gives the strict inequality in (4). This
proves \(D\ge AE\) also in the remaining branch. On positive exterior
gain it retains \(D/101\) in the physical comparison against \(168E\).
The previously established outer regions have positive margin at each
fixed spectrum. Homogeneity restores \(d\) in (1).

## A positive tied-middle branch example

Take \((h,k,q,p,b,c,d)=(20,1/2,4,1/10,11/10,21/20,1)\).
Then \(Z=41/100\) and \(H=g-b(h+3q)-(5/2)b^2=1671/40>0\).
The first strategy's test \((c-z)g\le(8/9)bcL\) fails strictly,
and the actual highest cut has zero width. The preceding optimized
[weighted highest residual](rank7_weighted_split_residual.md) is above
\(94\), also failing the preceding two-sided excess-ratio test.
Both applications of the shared coefficient in the second strategy
are therefore relevant to the comparison.

Even with the 21 additional pair caps, the 98-row packing relaxation
admits a strictly positive exterior gain \(11507/15000\) at this point.
In complementary triple notation put weight \(2/3\) on \(016,034,456\)
and \(1/3\) on \(015,025,026,124,135,136,145,234,235,236,246,356\).
All other weights vanish. This witnesses the limits of a
pure packing proof from those rows. The [exact checker](../verification/verify_rank7_fourth_third_product.py)
checks all 119 constraints at this rational array, its exact gain,
the earlier scalar test, both square estimates and the monotonicity
and endpoint comparisons used above.

## Transporting signed exterior certificates off the fourth–fifth tie

Now restore arbitrary \(d>0\). Fix the actual frame and the gaps
and weights \(h,k,q,b,c,d\), varying \(p=a-b\) from zero. The first
four weights increase together. Fix any three exterior prices
\(0\le\lambda\le g,\ 0\le\mu\le\Delta,\ 0\le\zeta\le Yq\) such that
\(C=XYq-\lambda(Y+q)-\mu q-\zeta(X+Y+q)\ge0\). Put
\(F(p)=E(p)-\lambda U(p)-\mu U_1(p)-\zeta U_\triangle(p)\).
Then **every coefficient of \(F(0)-F(p)\) in \(p\) is nonnegative**.
Moreover, with \(e=1-w_{0123}\), the difference dominates
coefficientwise the explicit polynomial
\[
\begin{split}
 e\big\{pC+p^4+Lp^3
 &+(g-\lambda)p(2p+2b-c-d)
   +(\Delta-\mu)p(p+b-c)\\
 &+(Yq-\zeta)p(3p+3b-c-d)\big\}. \tag{5}
\end{split}
\]
Thus a signed occupancy certificate obtained at \(a=b\) can be
used for every \(a\ge b\) along this fixed-gap family. For example,
a global comparison using only these prices and physical lower bounds
on the remaining mixed and anticommuting charges that are uniform in
\(p\) transfers directly. If the comparison uses a spectral compression
term, any decrease in its lower bound must also be paid.

For the proof take the exact three-price expansion with its three
auxiliary subtractions
\((g-\lambda)B_s,\ (\Delta-\mu)B_1,\ (Yq-\zeta)B_\triangle\).
The trace terms and the three prefactors do not vary with \(p\),
while \(D_A(p)=D_A(0)+pe\). The remaining exterior term is the
degree-zero and singleton-head contribution. All of its forward
monomials containing \(p\) are ordinary nonpositive-gain coefficients.
Among them, \(p^4\) and the three contributions yielding \(Lp^3\)
count only the top wedge and each has reference one per assignment.
This accounts for the corresponding terms of (5).
[Exact exterior expansion](rank7_three_price_head_expansion.md) ·
[Forward coefficients](rank7_forward_coefficients_independent.md)

For \(B_1\) the five-tail forward prefix gaps are \(p,b-c,c-d,d\).
Only terms containing prefix two vary. Their deficit coefficients
are nonnegative. The \(22\) and \(23\) terms alone pay
\([p^2+p(b-c)]e\). For \(B_s,B_\triangle\), in the six-row identities
all changes of the pair weights \(r_i r_j\) are coefficientwise
nonnegative. Here \(r_3=a\) and \(r_4,r_5,r_6=b,c,d\).
Write \(x=1-\sum_{i=3}^6 A_i,\ A_i=w_{012i}\), so that
\(e=x+\sum_{i=4}^6 A_i\).
In \(B_s\) the coefficient of \(x\) grows by
\(p(3b-c-d)+2p^2\), and the coefficient of \(A_i,\ i\ge4\),
grows by \(p(3b-r_i-c-d)+2p^2\). These dominate the shared
term in (5). In \(B_\triangle\) the increase outside of the
nonnegative pair-weight terms is
\[
 [p(2b-c-d)+3p^2]e+
     p\left[3D_A(0)+\sum_{i=4}^6 r_iA_i\right].
\]
The bracket dominates \(be\): its coefficient on \(x\) is \(3b\)
and on \(A_i\) is \(3b-2r_i\ge b\). All these comparisons hold
coefficient by coefficient, proving (5) and its monotonicity claim.
[Five-tail prefix formulas](rank7_harmonic_tail_transport.md) ·
[Shared and triangle six-row identities](rank7_three_price_head_expansion.md)

### Paying a decrease of the two actual compression widths

There is a sufficient test using only data on the initial tie.
Suppose its signed comparison \(AF(0)\le Q+96\sum_j\sigma_j(0)^2
\phi(s_j)\) uses the actual highest and shared cuts, along with a
remaining physical payment \(Q\) that is valid along the fixed-gap
family after restoring the signed charges. Here the traces \(s_j\)
are evaluated at the same frame and \(\phi(s)=\{s\}(1-\{s\})\).
The statement also allows the signed prices and \(Q\) to depend
on the frame when the test below holds for each such choice.
For the two positive raw excesses one has
\[
 \phi(s_1)=\phi(2+v)\le v\le e,\qquad
 \phi(s_s)=\phi(3+n+x)\le n+x\le2e .
\]
The other frames are covered by the [excess-axis comparisons](rank7_excess_ratio.md).
The two actual cut intervals are disjoint whenever both are active.
[Cut endpoints](rank7_near_three_tails.md)

Let \({\cal P}(p)\) be the polynomial in braces in (5).
Write \(a=b+p\) and let \(\alpha,\beta,\gamma\) increase with \(p\)
as before. In each row of the following table the candidate squared
width is \(m(p)[i(p)-o(p)]_+^2\).

| Cut | \(m(p)\) | \(i(p)\) | \(o(p)\) |
|---|---|---|---|
| Highest | \(\alpha\) | \(\sqrt{\beta cd}\) | \(\sqrt{b\gamma a}\) |
| Shared, first endpoint | \(\alpha\) | \(\sqrt{\gamma cd}\) | \(\sqrt{bca}\) |
| Shared, second endpoint | \(\gamma\) | \(\sqrt{\alpha cd}\) | \(\sqrt{b\beta a}\) |

For each row put \(K_i=2m(0)[i(0)-o(0)]_+o'(0)\). The initial
derivatives \(o'(0)\), in table order, are
\((\gamma(0)+b)/(2\sqrt{\gamma(0)}),\ \sqrt c/2,\
(\beta(0)+b)/(2\sqrt{\beta(0)})\). The inner endpoints and
prefactors increase. The outer endpoints are concave: in particular
the second derivative of \(\sqrt{(p+u)(p+v)}\) is
\(-(u-v)^2/[4((p+u)(p+v))^{3/2}]\).
Since \(s^2-(s-t)_+^2\le2st\) for \(s,t\ge0\), the fall in any
row's squared width is bounded by \(K_i p\). The actual shared width
is the minimum of its two rows, so its fall is bounded by
\(\max(K_2,K_3)p\).

Consequently the single initial slope test
\[
 A{\cal P}'(0)\ \ge\ 96[K_1+2\max(K_2,K_3)] \tag{6}
\]
transfers this certificate to **all \(p\ge0\)**. Indeed (5) pays
at least \(Ae p{\cal P}'(0)\), while the drop in the two payable
compression terms is at most its right side times \(ep\).
One can instead use the exact observed drop in each squared width
at a particular \(p\) if only that endpoint is of interest.

For illustration take \(d=1,\ b=6/5,\ c=11/10,\ (h,k,q)=(20,2,4)\)
and use \((\lambda,\mu,\zeta)=(rg,r\Delta,0)\) as above.
Both initial true widths are positive. Even dropping the subtracted
outer endpoint from each \(K_i\) gives \(K_1<220,\ K_2<100,\ K_3<100\)
by rational squared comparisons. Meanwhile \(AC>96(220+200)\),
so the cubic completion term alone passes the initial slope test.
This example checks that (6) can pay two initially active cuts.
