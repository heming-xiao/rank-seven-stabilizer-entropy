# Full shared compression and an endpoint comparison for the sixth probability

## The shared crossing can be paid after either exterior estimate

For the remainder set \(a=b,\ q\ge b/2,\ d=1\). Keep the notation
\(g=hq,\ X=h+k+q,\ Y=k+q,\ \Delta=kX,\ A=1.01\cdot168\).
Let \(s\le3g/2,\ t\le7\Delta/4\), with both nonnegative, and
\(\lambda=24s/A,\ \mu=24t/A\). Thus \(\lambda<g/2,\ \mu<\Delta/2\)
when their respective spectral gaps are positive. The only entering
wedge for the shared nominal interval is \(1234\). Its correction
is at most
\[
      D_\times(c)={\gamma h\over2}(b-c)w_{1234}.
\]
This follows from the per-wedge error in (2) of the
[nominal-width analysis](rank7_full_nominal_widths.md).
The shared auxiliary deficit \(B_s=cn-U^0\) is at least
\((b^2-c)w_{1234}\ge(b+1)(b-c)w_{1234}\);
the completion deficit satisfies \(D_A\ge (b-c)w_{1234}\).

In the signed singleton estimate the unused \((g-\lambda)B_s\)
alone pays \(96D_\times/A\):
\((A-36)q(b+1)\ge48(b+q)\). This leaves the completion-price
interpolation \( \min(q,cC)(2n+v-3M)_+\) in place, with
\(C=XYq-\lambda(Y+q)-\mu q\). In the tied-middle split, retain
the previously dropped terms. Writing \(B=cn-U=B_s+(Y+q)D_A\),
the coefficient on \(B_s\) is \(g/2-\lambda\), and the retained
coefficient on \(D_A\) is
\[
 (g/2-\lambda)(Y+q)+q(\Delta-\mu)
     +kq(q+2b-c-1)-kg/2\ \ge\ (g-2\lambda)q.
\]
Indeed \(q(\Delta-\mu)\ge kg/2\ge k\lambda\) and \(2b\ge c+1\).
Together these terms pay \(96D_\times/A\), since
\[
   (A/2-36)q(b+1)+(A-72)q^2\ge48(b+q).
\]
The difference is increasing in \(q\); at \(q=b/2\) it is
\(48.84b^2-47.58b>0\). The two payments accompany two alternative
upper bounds on the same frame. Their convex combination pays the
crossing exactly once. The shared Pauli, highest Pauli and rank-six
anticommuting slots remain those of the three-variable payment.

## Elimination of the sixth probability

Write \(z=h/b,\ y=k/b,\ x=q/b,\ G=zx,\ D=y(z+y+x)\), and
\[
     m=\min(1+x,1+z/(1+x+y)),\qquad
     V=(1+x+y+z)(1+x)(1-\sqrt{b/m})_+^2.
\]
The shared nominal width squared is \(cb^2 V\), which is affine
in \(c\). The gain \(E(c)\), probe differences \(U(c),U_1(c)\)
and crossing allowance \(D_\times(c)\) are affine as well. For
the gains, each wedge product uses the sixth probability at most
once.

Here is an optional simultaneous use of the direct and rank-six
matching inequalities that also preserves affinity. Allocate a
fraction \(f\in[0,1]\) to the rank-six correction, leaving \(1-f\)
for the direct estimate \(\langle p s_6\rangle\le5+(200/11)\kappa\).
The bilinear term in the rank-six subtraction then has factor \(f\),
so its square cost has factor \(f^2\). Set
\[
  Q_f=1+{72f^2\over z^2+x^2},\qquad
  G_c=G-(1-f)(200/11)(c-1)/b,\qquad \bar s=s/b^2.
\]
These give the lower quadratic coefficient on \(P=\max(n,v)\)
in units of \(A b^4\):
\[
  S(c)=\{G^2/12+\bar s(2G_c-Q_f\bar s)\}/A.
\]
Choose \(\bar s\le(3/2)(G_{c_{\rm max}})_+/Q_f\) so the use of
\(\kappa\ge P/12\) is valid. This allocation uses only one
rank-six reserve. [Direct estimate](rank7_triangle_probe_tail_equalization.md) ·
[Rank-six estimate](rank7_six_mode_shared_probe.md)

Fix the spectrum other than \(c\) and fix \(s,t,f\). After the
crossing payment above,
\[
       \big(E(c)-\lambda U(c)-\mu U_1(c)+96D_\times(c)/A\big)/b^2
\]
is an affine function bounded by either signed exterior estimate.
The common mixed and anticommuting payment divided by \(Ab^2\) is
at least \(b^2[S(c)P+T v]\), with \(T\) as in the three-variable
proof. Add \(96cV F_s/A\) from compression, with \(F_s\) the
unrounded shared-cut fractional trace loss. For \(n>0\),
\(F_s\ge n(1-\min(1/2,n/(3v)))\). This also follows directly
from \(\phi(n+x_{\rm comp})\ge n(1-n)\) when
\(2n+x_{\rm comp}\le1\), using \(n\le1/2,\ v\le1/3\).
The resulting payment is affine in \(c\) for a fixed physical
frame. Consequently it suffices to compare at the two tail
endpoints \(c=1,\min(b,9/5)\). The signed bounds at the endpoints
can use different convex-combination coefficients. The physical
shifts \(s,t,f\) are held fixed between those endpoints.

For each tail endpoint retain in both exterior estimates the
highest-pair prefix deficit
\((\Delta-\mu)(b-1)(c-1)\max(v,n/2)\).
In the singleton branch also retain \(Z=\max(5n/2,2v,2n+v)\)
and its completion interpolation. As functions of \(r=v/n\)
with \(n=1\), all the terms in either margin are affine between
\[
             0,\ 1/2,\ 2/3,\ 1,\ 2,\ 4,\ \infty
\]
except for the shared trace bound, which is constant on the first
part and concave \(1-1/(3r)\) past \(2/3\). Thus on each interval
a common endpoint-wise convex-combination coefficient giving
nonnegative margins on its two bounding rays is sufficient. On
the last interval the infinite ray checks the limiting slope.
The chosen \(s,t,f\) may also change between ratio intervals,
since the ratio belongs to the given physical frame.

For example every spectrum proportional to
\[
       (649/40,253/40,11/2,11/10,11/10,c,1),
               \qquad 1\le c\le11/10
\]
passes this endpoint test with strict margins. The shared nominal
width is positive; the highest compression width is entirely
omitted. The [exact rational example](../verification/verify_rank7_positive_shared_tail_endpoints.py)
uses an upper rational square root inside \(1-\sqrt{b/m}\).
It checks the two tail endpoints on each of six adjacent ray
pairs. Every normalized margin is greater than \(1/4\)
(smallest certified grid choice approximately \(1.69885\)).
These strict comparisons also give an open neighborhood of this
compact spectral segment by the existing optimizer stability theorem.

## An exact scalar obstruction to using the rank-six correction alone

At \(c=b=11/10\) in the example take the exterior ray \(n=v=1\)
in homogeneous units. Set \(D_0=1-(b-1)(c-1)\), \(H'=G-z-3x-5/2\),
\(R'=y^2(y^2+(z^2+x^2)/2)\), \(K=5/2\). The above comparison
restricted to \(f=1\) has negative margin even after optimizing both
physical shifts over the entire real line. Indeed the completion
interpolation vanishes on this ray. The best of the two exterior
branches has the same shift-dependent terms. Completing the two
independent negative squares bounds its best possible margin by
\[
 {b^2(G+12c/b^2)^2\over A Q_1}
 +{12b^2(D+K D_0/b^2)^2\over A K}
 +{b^2(G^2/12+R'/K)\over A}-DD_0+{64cV\over A}
 +\max\{c(z+2y+3x)+3/b^2-cG,\ cy-cH'\}.
\]
Since \(\sqrt{b/m}>13/20\), the expression is strictly below
\(-832508132851/222066324480<-37/10\) by rational substitution.
Thus the direct matching option supplies a genuine improvement
in this particular endpoint comparison. The obstructed scalar
relaxation includes the shared compression and omits the highest
compression as throughout the example. No violating physical frame
is implied.
