# Eliminating the two nominal compression corrections on spectral cones

November 18, 2026. Both nominal squared compression widths of the
[crossing inequality](rank7_crossed_compression.md) can be used at
their full values in the paired comparison, including where both
true upper-set tests fail. Two sufficient spectral regions are
\[
 \gamma-a\ge\max(a,8d/5),\qquad\text{or}\qquad
 a=b,\quad \gamma-b\ge\max(b/5,2d/5). \tag{1}
\]
The first allows all seven probabilities to differ. In the second,
the entire currently unresolved \(a=b\ge2d\) subregion qualifies,
because the [small-shared comparison](rank7_small_shared_gain.md)
already covers \(\gamma-b\le b/5\). These statements remove
the crossing correction within a specific joint inequality.
The remaining scalar comparison of exterior gain against all the
physical payments is still required for a full entropy-optimality
theorem throughout either cone.

Write \(A_*=(101/100)168,\ h=\alpha-\beta,\ k=\beta-\gamma,\
q=\gamma-a,\ p=a-b,\ X=\alpha-a,\ Y=\beta-a,\ g=hq,\ \Delta=kX,\
J=Yq\). Use physical shifts \(0\le s\le g,\ 0\le t\le\Delta\)
and zero triangle shift. The signed exterior prices are
\(\lambda=24s/A_*,\ \mu=24t/A_*\), and the completion coefficient is
\(C=XYq-\lambda(Y+q)-\mu q\). Since
\(g(Y+q)+\Delta q\le2XYq\), we have
\(A_* C\ge(A_*-48)XYq\).
[Same-frame exterior expansion](rank7_three_price_head_expansion.md)

## Four points on a crossing row

Write \(u_j,l_j,r_j,\sigma_j=(u_j-l_j)_+\) for the endpoints,
per-wedge error, and amplitude width of either nominal cut from the
crossing inequality (\(j=1,s\)). In that normalization
\(\mathcal D_F\ge\sigma_1^2F_{R_1}+\sigma_s^2F_{R_s}\) minus
the six entering wedge errors multiplied by \(w_I(1-w_I)\).
The highest error is bounded above on either bad wedge with
fourth index \(i=4,5,6\) by
\[
 r_1(A_{023i})\le \frac{\alpha k d}{2}
          [p+(b-c){\bf1}_{i=4}]. \tag{2}
\]
The shared error obeys the same bound with \(\gamma h\) in place
of \(\alpha k\), and it only charges \(123i\). To prove this use
\(r_j(z)\le2\sigma_j(z-l_j)_+\).
For the first cut \(\sigma_1=\sqrt{\alpha c}
(\sqrt{\beta d}-\sqrt{\gamma b})_+\) and
\[
 2\sqrt{\gamma b}(\sqrt{\beta d}-\sqrt{\gamma b})_+
 \le(\beta d-\gamma b)_+\le kd.
\]
At \(i=4\) the resulting bound is
\(\alpha kd\sqrt c(\sqrt a-\sqrt c)\le\alpha kd(a-c)/2\).
At \(i=5\) it is
\(\alpha kd(c/\sqrt b)(\sqrt a-\sqrt b)\le\alpha kd\,p/2\);
the \(i=6\) amplitude is no larger. For the shared cut use
\(\sigma_s\le\sqrt{\gamma c}(\sqrt{\alpha d}-\sqrt{\beta b})_+\)
and \(l_s\ge\sqrt{\beta\gamma bc}\), obtaining the same calculation.

Let \(M_i=w_{023i}+w_{123i}\), \(e=1-w_{0123}\),
\(A_i=w_{012i}\), \(x=1-\sum_{i=3}^6 A_i\).
The complement \(56\) row and the two triple capacities give
\[
 M_4\le1-A_3-A_4=x+A_5+A_6,\qquad \sum_iM_i\le2e .
\]
The completion price decomposes as
\[
 D_A=pe+(b-c)(x+A_5+A_6)+c x+(c-d)A_6
                    \ge pe+(b-c)M_4+c x . \tag{3}
\]
Consequently the total crossing error in \(\mathcal D_F\) is at most
\(d(\alpha k+\gamma h)[pe+(b-c)M_4]\). We used
\(w_I(1-w_I)\le w_I\). The following spectrum-only test therefore
removes all six errors in the physical purity units:
\[
 A_* C\ge96d(\alpha k+\gamma h)
 \ \Longrightarrow\
 96\mathcal D_F+A_* C(D_A-cx)
 \ \ge\ 96[\sigma_1^2 F_{R_1}+\sigma_s^2 F_{R_s}]. \tag{4}
\]
The geometric interpolation may still spend \(Ccx\). The three
auxiliary deficits \(B_s,B_1,B_\triangle\), the signed trace terms,
and the pure tail and singleton terms remain available separately.
The portion \(C(D_A-cx)\) has been allocated in (4).

For the first cone in (1),
\(\alpha k+\gamma h=Xk+qh+a(h+k)\le2XY\): the first two
terms sum to at most \(XY\), and \(a\le q\) bounds the last one.
The exact inequality \((A_*-48)(8/5)>192\) proves (4).

## A second complete payment when the fourth and fifth weights coincide

Set \(p=0\), \(a=b\). All crossing errors with \(i=5,6\) vanish.
There is a further bound for the remaining shared error,
\[
  r_s(A_{1234})\le \gamma h d\sqrt c(\sqrt b-\sqrt c)
                   \le \tfrac14\gamma h(b^2-cd). \tag{5}
\]
For \(b>c\), divide the middle expression by
\(b^2-c^2\le b^2-cd\); the factor
\(d\sqrt c/[(\sqrt b+\sqrt c)(b+c)]\le1/4\).
For \(b=c\) the error vanishes directly.

The explicit [six-row weighted deficits](rank7_three_price_head_expansion.md)
supply independent costs on these two wedges:
\[
 B_s\ge (b^2-cd)w_{1234},\qquad
 B_\triangle\ge (2b-d)(b-c)M_4. \tag{6}
\]
The first summand is the tail-pair \(34\) term
\((r_3r_4-cd)B^{12}_{34}\). For the second bound retain
\((2b-c-d)D_A+\sum_i r_i(b-r_i)A_i\) in \(B_\triangle\).
Its coefficients on \(x,A_5,A_6\), respectively, are
\(b(2b-c-d),(b-c)(2b-d),(b-d)(2b-c)\).
Each dominates \((2b-d)(b-c)\): the two differences that can be
nonzero are \(c(b-d)\) and \(b(c-d)\). Apply the first row of (3).

If \(q\ge b/5\), then \(\gamma=b+q\le6q\). Thus
\(96r_s(A_{1234})\le144g(b^2-cd)\), which is paid by
\(A_*(g-\lambda)B_s\) since \(A_*-24>144\).
The highest crossing error costs at most
\(48\alpha k d(b-c)M_4\) in physical units.
By (3) and (6) we may pay from
\(A_*[C(D_A-cx)+J B_\triangle]\), whose coefficient on
\((b-c)M_4\) is at least
\[
 A_*[C+J(2b-d)]\ \ge\ (A_*-48)(X+b)Yq
                       =(A_*-48)\alpha(k+q)q .
\]
This covers \(48\alpha kd\) throughout \(q\ge2d/5\).
Combining the payments proves the second cone in (1). The entire
highest-pair auxiliary deficit, including its harmonic-tail price,
and the geometric \(Ccx\) reserve can still be used. The indicated
parts of \(B_s,B_\triangle\) have been spent once.

This use of physical occupancies is necessary for a basis-invariant
argument. Both remaining wedges contain the whole tied plane
\(\operatorname{span}(x_3,x_4)\). A change of basis in that plane
only multiplies their four-wedge vectors by a determinant of
modulus one, so their occupancies and variances do not change.
For instance take standard computational modes in dimension eight
except \(x_1=(|1\rangle+|4\rangle)/\sqrt2\) and
\(x_4=(|1\rangle-|4\rangle)/\sqrt2\). Mode \(0234\) then
has occupancy \(1/2\), because its \(0123\) component is a plane
and its \(0234\) component is not. Its variance remains \(1/4\)
under every allowed basis change in the doublet.

## Strict crossings in both cones

The first cone contains \((9.5,5.8,3.6,1.6,1.5,1.2,1)\).
The tied cone contains \((6.6,3.9,2.3,1.5,1.5,1.2,1)\), where
\(q=0.8\) lies below the first cone. At both spectra the nominal
highest and shared widths are strictly positive, while both actual
upper-cut widths are zero. All four comparisons are strict and
persist in their respective spectral families.
The [exact verifier](../verification/verify_rank7_full_nominal_widths.py)
checks the two row prices on every four-wedge, the three
rational constants and all the displayed strict crossings.

## An extra highest-pair price on both crossing wedges

On arbitrary ordered tails set \(M=M_4=w_{0234}+w_{1234}\).
The highest tied-four-head deficit \(B_1=d^2v-U_1^0\) satisfies
\[
 \boxed{B_1\ge p(a-c)e+(b-d)(c-d)d_1+(a-c)(b-d)M,}
 \qquad d_1=2-I_4. \tag{7}
\]
Here \(I_j\) is the total internal mass of edges \(w_{01kl}\)
on the first \(j\) labels of \(2,3,4,5,6\). In the
[five-tail prefix expansion](rank7_harmonic_tail_transport.md)
write \(\delta_{ij}=P^*_{ij}-P_{ij}\). The physical row on
complementary pair \(56\) is exactly \(I_3+M\le1\).
Since \(P_{23}=w_{0123}+I_3\) and \(P_{34}=I_3+I_4\),
we obtain \(\delta_{23}\ge e+M,\ \delta_{34}\ge d_1+M\),
and \(\delta_{33}/2=1-I_3\ge M\).
The sum of the two complementary pair rows on \(46,56\)
covers \(P_{24}+M\) with capacity two, giving \(\delta_{24}\ge M\).
The additional coefficients of \(M\) are
\(p(b-c)+(b-c)(c-d)+(b-c)^2+p(c-d)=(a-c)(b-d)\).
The previous \(\delta_{22}/2=e,\ \delta_{44}/2=d_1\) and
the previous parts of \(\delta_{23},\delta_{34}\) are all retained.

On \(a=b,\ q\ge b/5\) the two widths can consequently be used in
full whenever
\[
                         b\ge 11d/10. \tag{8}
\]
The earlier comparison already covers \(q\ge2d/5\).
The shared crossing is paid by (5). For the highest crossing we
retain \(Ccx\) and both old terms of (7), spending only its last
term with coefficient \(A_*(\Delta-\mu)\ge(A_*-24)kX\).
If \(k=0\) or \(b=c\) this crossing vanishes, so suppose \(k>0,b>c\).
The additional coefficient after division by \(\alpha k d(b-c)\)
is at least \((A_*-24)(b/d-1)X/(X+b)\).
Set \(\eta=b/d,\ z=k/b>0\). Since \(X\ge k+q,\ q\ge b/5\), the
combined coefficient including the original completion and triangle
prices is at least
\[
 P_\eta(z)=\frac{(A_*-48)\eta}{5}\left(1+\frac{1}{5z}\right)
       +(A_*-24)(\eta-1)\frac{z+1/5}{z+6/5}.
\]
It suffices that \(P_\eta(z)\ge48\). A smaller target follows by
retaining the root denominator in (2). In fact
\(\beta d-\gamma b=kd-\gamma(b-d)\) and the root-difference
multiplier is \(2/[1+\sqrt{\beta d/(\gamma b)}]\) whenever this
difference is positive. Using \(6/5\le\gamma/b\le7/5\) on
\(b/5\le q<2d/5\), a sufficient condition is
\[
 P_\eta(z)\ge 48
 \left(1-\frac{6(\eta-1)}{5z}\right)_+
 \min\left(1,\frac{2}{1+\sqrt{(1+5z/7)/\eta}}\right). \tag{9}
\]
For \(\eta\ge6/5\), \(P_\eta\ge P_{6/5}\) and
\[
 P_{6/5}(z)-48=
 \frac{6(26925z^2-28355z+18252)}{3125z(5z+6)}>0
\]
by the negative discriminant.
For \(11/10\le\eta\le6/5\) use \(P_{11/10}\), replace \(\eta\)
by \(11/10\) in the positive part and by \(6/5\) under the square
root. For \(0<z\le7/25\) the left side exceeds \(45\) and the right
side is below \(28\), by these endpoint substitutions.
For \(z\ge7/25\) let \(w=\sqrt{(5/6)(1+5z/7)}-1\ge0\).
The lower bound for left minus right is
\[
 \frac{12\,Q(w)}{4375(w+2)(6w^2+12w+1)(42w^2+84w+37)}
\]
with coefficients of \(Q\) in ascending order
\((625564,-2637822,392532,13769553,13967352,3797892)\).
The polynomials \((1+y)^5 Q(y/[4(1+y)])\) and \(Q(y+1/4)\)
have strictly positive coefficients. These substitutions cover the two
intervals on either side of \(w=1/4\), including the joining point.
The verifier checks the polynomial identity at six rational points and
both sets of coefficients exactly. In particular the tied spectra still
needing a crossing correction satisfy \(b<11d/10,\ q<2d/5\) after
the previously established \(q\le b/5\) optimality theorem.

