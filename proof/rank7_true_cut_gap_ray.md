# Transport of both actual rank-seven cuts along the fourth-gap ray

November 18, 2026. Fix \(h=\alpha-\beta,\ k=\beta-\gamma,\
q=\gamma-a,\ b,c,d\) and vary \(p=a-b\ge0\), so that all four
largest Schmidt weights increase together. Suppose that at \(p=0\)
there is a signed paired certificate using the two **actual** highest
and shared compression widths and a remaining payment valid on this
ray. For \(A=(101/100)168\), physical shifts \(0\le s\le g=hq,\
0\le t\le\Delta=kX\), and zero triangle shift, the following hold.
Here \(Y=k+q,\ X=h+Y\).

* If \(q\ge96cd/[(A-48)b]\), the same certificate transfers to
  every \(p\ge0\). In particular \(q\ge4d/5\) suffices.
* If \(q\ge3d/5\), the initial certificate implies global
  optimality along the entire ray. The transferred certificate covers
  all points below the fourth-gap product threshold, and the existing
  product theorem covers the remaining points.

Thus a proof on \(a=b\) with the stated signed payments removes the
fourth-gap variable on either indicated region. These are conditional
transfers from the specified seed comparison. No arbitrary fourth-gap
variation of a physical remainder is assumed.
[Signed exterior transport](rank7_fourth_third_product.md)

## Both rounded traces cost at most the same top-wedge deficit

Let \(s_1=L_{01},\
s_s=\sum_{I\ni 0,\ I\cap\{1,2\}\ne\varnothing}w_I\), and
\(e=1-w_{0123}\). It suffices to consider positive raw excesses
\(v=L_{01}-2,\ n=L_{01}+L_{02}-4\). For
\(x=1-\sum_{j=3}^6 w_{012j}\) one has \(s_s=3+n+x\). The
directed row \((3,0)\) and the two complementary four-set rows on
\(1456,2456\) cover \(s_s+w_{0123}\) at capacity four.
Consequently \(n+x\le e\). The existing highest row gives \(v\le e\).
Thus each of \(\phi(s_s)\) and \(\phi(s_1)\) is at most \(e\), where
\(\phi(s)=\{s\}(1-\{s\})\). The other excess sectors already
satisfy the paired comparison. [Excess axes](rank7_excess_ratio.md)

For signed prices \(\lambda=24s/A,\ \mu=24t/A\) let
\(F(p)=E(p)-\lambda U(p)-\mu U_1(p)\).
Write \(\alpha_0=b+X\) and \(S=cd\). The transfer from the seed
needs to pay at most the decreases in its two squared widths,
multiplied by \(96e\). The initial slope in the signed exterior
comparison is at least
\[
 A[C+Yq(3b-c-d)]\ge(A-48)\alpha_0Yq,\quad
 C=XYq-\lambda(Y+q)-\mu q.
\]
Indeed \(g(Y+q)+\Delta q\le2XYq\) and \(3b-c-d\ge b\).
The signed exterior polynomial therefore pays at least
\((A-48)\alpha_0Yq\,pe\) at any point of the ray. This uses
only its cubic completion and triangle deficit.
[Coefficientwise fourth-gap bound, equation (5)](rank7_fourth_third_product.md)

## Derivatives on the active physical endpoints

Denote current weights by \(a=b+p,\ \gamma=a+q,\ \beta=a+Y,\
\alpha=a+X\). The highest squared width is \(W_1\); the shared
squared width is \(\min(W_2,W_3)\), with
\[
\begin{aligned}
 W_1&=\alpha[\sqrt{S\beta}-\sqrt{ab\gamma}]_+^2,\\
 W_2&=\alpha c[\sqrt{d\gamma}-\sqrt{ab}]_+^2,\\
 W_3&=\gamma[\sqrt{S\alpha}-\sqrt{ab\beta}]_+^2 .
\end{aligned}
\]
In particular \(W_3\) can be the active positive branch only when
\(\beta\gamma\ge\alpha c\), since these two outside scores share
the factor \(ab\). Integration below uses the active derivative;
it permits switches between the two true outside endpoints.

For the first and third rows set
\[
 f(a)=[\sqrt{S}\sqrt{t+u}-\sqrt{ab}\sqrt t]_+^2,\qquad t=a+y,
 \quad \xi=\sqrt{1+u/t},\quad R=\sqrt{ab/S}\ge1.
\]
On the positive branch \(\xi>R\), direct differentiation gives
\[
 -f'(a)=S(\xi-R)[R-1/\xi+Rt/a].
\]
The first upper bound, retaining the actual gap when \(R>1\), is
\[
 -f'(a)\le\frac Sa[u-t(R^2-1)]\frac{2R-1/\xi}{R+\xi}
       \le\frac Sa[u-t(R^2-1)](1-1/(2\xi^2)).                 \tag{1}
\]
This uses \(a/t\le1\) and monotonicity of the fraction in \(R\).
There is also a bound on the unrestricted gap alone,
\[
                  -f'(a)\le(4-2\sqrt3)Su/a .                    \tag{2}
\]
Indeed the ratio to \(Su/a\) is at most
\((\xi-R)(2R-1/\xi)/(\xi^2-1)\). Its maximum over
\(1\le R\le\xi\) occurs at \(R=1\) or at
\(R=\xi/2+1/(4\xi)\) when that point is above one. At \(R=1\)
maximize \((2-1/\xi)/(\xi+1)\), obtaining \(4-2\sqrt3\) at
\(\xi=(1+\sqrt3)/2\). The interior maximum is
\(1/2+1/[8\xi^2(\xi^2-1)]\), decreasing in \(\xi\) on its
domain. At the first admissible \(\xi\) it equals the boundary
value. Nonpositive branches have zero derivative. For increasing
prefactor \(m\) multiplying \(f\), the negative derivative of
\(mf\) is bounded above by \(-mf'\) wherever \(f\) is positive.

For \(W_1\), (2) yields
\[
           -W_1'\le(4-2\sqrt3)\alpha_0 S k/b .                 \tag{3}
\]
Here \(\alpha/a\le\alpha_0/b\). For \(W_2\), write
\(\xi=\sqrt{1+q/a},\ R=\sqrt{b/d}\). On its positive branch
the derivative loss of its bracket squared is
\(d(\xi-R)(R-1/\xi)\le d q^2/[4a(a+q)]\), by maximizing the
product of the two nonnegative factors with fixed sum.
Dropping the negative derivative of its inner root also bounds that
loss by \(dq/(2a)\), using
\(\sqrt{d\gamma}-\sqrt{ab}
 \le[dq-(b-d)a]/[2\sqrt{ab}]\).
Consequently
\[
      -W_2'\le \alpha_0 S\min\{q/(2b),q^2/[4b(b+q)]\}.          \tag{4}
\]
In particular this endpoint alone always costs less than the signed
exterior slope since \(S\le b(b+q)\), \(Y\ge q\) and \(24<A-48\).

For \(W_3\) on its active positive branch use (1) at
\(u=h,\ t=\beta\). Activity gives
\[
 \gamma h-\alpha q=\alpha a-\beta\gamma\le\alpha(a-c),
 \qquad \gamma\beta(R^2-1)\ge\alpha(ab/d-c)\ge\alpha(a-c).
\]
Thus \(\gamma[h-\beta(R^2-1)]\le\alpha q\).
In addition \(\xi^2=\alpha/\beta\le\gamma/c\). It follows that the
active derivative satisfies
\[
             -W_3'\le\frac{\alpha_0 S q}{b}
                      \left(1-\frac{c}{2\gamma}\right).         \tag{5}
\]
The signed initial slope pays the sum of (3) and the larger active
bound (4) or (5) for the first theorem, since the sum is at most
\(\alpha_0 S(k+q)/b\). These widths are locally Lipschitz and their
minimum is absolutely continuous on finite intervals. Integrating
their bounds yields the stated global comparison.

## Transfer on the whole unsolved part of a fourth-gap ray

If \(p(p+q)\ge(2/5)d^2\), the
[fourth-gap product theorem](rank7_fourth_third_product.md)
already gives global optimality. Otherwise write
\[
 z=q/d,\quad U(z)=\frac{z+\sqrt{z^2+8/5}}2,\quad
 \omega(z)=1-\frac{1}{2(1+U(z))}.
\]
At all earlier points on the segment one has \(p+q\le dU(z)\).
The function \(c(1-c/(2\gamma))\) increases for \(0\le c\le b\le\gamma\).
Thus \((c/b)(1-c/(2\gamma))\le1-b/(2\gamma)\le\omega(z)\).
Equation (5) now costs at most \(\alpha_0qd\omega(z)\).
In (3) the constant \(4-2\sqrt3<27/50\) also lies below \(\omega(z)\)
because \(U(z)\ge\sqrt{2/5}>1/2\). The linear bound in (4) is smaller
still. The two losses on this entire segment are therefore paid if
\[
                    z\ge\frac{96}{A-48}\,\omega(z).             \tag{6}
\]
Since \(0<U'(z)<1\), the derivative of the right side is below
\(48/(A-48)<1\). At \(z=3/5\), \(U=1,\ \omega=3/4\) and
\(72/(A-48)<3/5\). Hence (6) holds for every \(q\ge3d/5\).
The comparison uses identical mixed and anticommuting charges as
the assumed seed and the actual two independent compression cuts.
Its axes and product-covered regions use their existing paired
arguments. The [exact checker](../verification/verify_rank7_true_cut_gap_ray.py)
checks the new occupancy row, the derivative and branch algebra,
and the rational constants.

### Seeds using larger shifts

For \(s\le m_sg,\ t\le m_t\Delta\), suppose the original seed has
a valid physical remainder on the ray and the corresponding signed
prices obey the hypotheses of the exterior transfer. In (6), and in
the direct all-\(p\) test, \(A-48\) can be replaced by
\[
 A-24\max(2m_s,m_s+m_t)
\]
when positive. Indeed, dividing the signed cubic debit by \(XYq\)
after multiplication by \(A/24\) gives an upper bound
\(m_s(h/X)(1+q/Y)+m_t(1-q/Y)\) when \(XYq>0\).
Use \(h/X\le1\) and maximize the resulting affine function on
\(0\le q/Y\le1\). The degenerate case has zero cubic debit.
In particular for \(m_s=m_t=5/4\) the denominator is \(A-60\),
and \(q\ge2d/3\) implies optimality on the whole ray by the seed
and the product theorem. At \(z=2/3\) one has \(U(z)<21/20\),
so the right side of (6) with this denominator is below
\(96(31/41)/(A-60)<2/3\); its derivative is below one.

## An entire ray with an explicit seed

The sorted representative is globally optimal at **every**
\(p\ge0\) for the spectra given by
\[
       (h,k,q,b,c,d)=(5,1,3/5,26/25,51/50,1),\qquad a=b+p .
\]
At \(p=0\) use \(s=t=1\). A rational packing dual with 25 nonzero
row prices verifies on all 35 wedges
\[
                   AE-24U-24U_1\le 15n+110v
\]
on the two-positive-excess sector. The first mixed and anticommuting
payments are at least \(4n+64v\) after the two linear charges.
Indeed their respective coefficients per unit excess are
\([12(2(g-\tau)-1)+g^2]/12\) and
\([12(2\Delta-1)+R]/(5/2)\), where
\(\tau=200b(c-1)/11,\ R=k^2[k^2+(h^2+q^2)/2]\).
These payments are uniform in \(p\). On positive seed gain the
actual two widths furnish the remaining \(11n+46v\): here
\(\phi(s_1)\ge2v/3,\ \phi(s_s)\ge\omega_0 n\) with
\(\omega_0=(aXYq-\Delta/3)/(cg+2aXYq)\). The checker verifies
\(64W_1>46,\ 96\omega_0\min(W_2,W_3)>11\) at the tie by squaring
rational numbers. At a positive-gain frame after increasing \(p\),
the seed gain is positive by the unpriced exterior monotonicity,
so this positivity restriction also transfers. The second theorem
above and the already solved axes complete the ray.
[Seed trace estimates](rank7_uniform_cut_packing.md) ·
[Physical payments](rank7_two_probe_separation_and_tail_region.md)
