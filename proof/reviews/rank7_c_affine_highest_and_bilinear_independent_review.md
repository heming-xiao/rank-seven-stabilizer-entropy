# Independent review of the two-cut affine tail comparison

November 18, 2026.

## Varying \(c\) at fixed \(d\)

Scale \(a=b=1\) and fix \(h,k,q,d\) and the frame.
The two true highest endpoints squared are \(Uc,L\), where
\(U=\alpha\beta d\), \(L=\alpha\gamma\).
The true squared width is
\[
  W_1(c)=(\sqrt{Uc}-\sqrt L)_+^2.
\]
On its positive part the second derivative is
\(\sqrt{UL}/(2c^{3/2})\), and the first derivative matches
zero where the active part starts. The entire width is
nondecreasing and convex. A convenient rational affine
lower bound for \(\theta\ge0\) is
\[
  W_1(c)\ge \theta(Uc-L)-\tfrac{\theta^2}{2}(Uc+L).
\]
When \(Uc\ge L\) the maximum of the right side is
\((Uc-L)^2/[2(Uc+L)]\), which bounds the true width below.
When \(Uc<L\) every such line is nonpositive. On a subinterval
\([\ell,u]\), choosing
\(\theta=(U\ell-L)_+/(U\ell+L)\) makes the line nonnegative
throughout the subinterval. Any positive crossing threshold
\(L/U\) inside the interval can be used as a subdivision
endpoint.

The paid nominal shared width is exactly \(c W_s\), with
\(W_s=(\sqrt{\alpha\gamma d}-\sqrt{\max(\alpha,\beta\gamma)})_+^2\).
Its upper endpoint squared is \(\alpha\gamma cd\le L\),
so it is disjoint from the true highest interval.
At \(p=0\), the shared crossing allowance is
\(D_\times(c)=\gamma h d(1-c)w_{1234}/2\).
Both exterior upper bounds of the existing comparison have
already paid this crossing. The true highest cut adds no
crossing allowance.
[Paid nominal comparison](../rank7_positive_shared_tail_endpoints.md) ·
[Disjoint allocation](../rank7_crossed_compression.md).

With a fixed rank-six mixing fraction \(f\), the direct
shared correction is affine in \(c-d\). The square penalty
after the rank-six contribution uses the bound
\[
 \Psi_0=(h^2+q^2+d^2)/6+(1-d)^2/7,
\]
because \((c-d)^2+(1-c)^2/6\ge(1-d)^2/7\).
Thus a fixed conservative \(Q_f=1+12f^2/\Psi_0\) gives
an affine lower bound on the mixed receipt with fixed
shifts. The independent odd-cut factor
\((1-c)^2+d^2\) can be replaced by its tangent at the
right endpoint \(u\), which is nonnegative for \(c\le u\).
The two compression lower prices then preserve affinity
with the frame and trace factors fixed.
The actual signed exterior quantity
\(E-\lambda U-\mu U_1+96D_\times/A\) is itself affine in \(c\).
Its two exterior estimates need only be evaluated at the
endpoints. Different convex weights there are allowed,
while the physical shifts and \(f\) are shared.

An exact example uses \((h,k,q,d)=(14,1,4,19/20)\), the
entire interval \(c\in[19/20,1]\), and common direct-mode
shifts \(u=13/20,w=1\). With the highest affine support,
all twelve endpoint-sector comparisons have margin greater
than \(1/16\). Dropping that line at the same fixed shifts
leaves the smallest endpoint-sector margin below \(-1/40\).
The comparison is between sufficient prices with these
shifts.
[Exact endpoint example](../../verification/verify_rank7_c_affine_highest.py).

## Bilinear C++ extension

For a rectangle in \(c,d\), the actual signed exterior gain
and \(D_\times=\gamma hd(1-c)w_{1234}/2\) are multiaffine.
The true highest affine support in \(Ucd\), and the nominal
shared support \(c\,\ell(d)\), are also multiaffine.
Their weights chosen at the lower corner keep them nonnegative
throughout the rectangle. The physical mixed slope is affine
in \(c-d\). Its common rank-six correction uses the bound
\(\Psi_{\rm tail}\ge1/13\), since for
\(x=1-c,y=c-d,z=d\),
\[
 x+y+z=1,\qquad y^2+(x^2+z^2)/6\ge1/13
\]
by weighted Cauchy–Schwarz. A lower bound read from the
outward corner coordinates can only improve this bound.
The odd-cut factor uses the sum of two nonnegative affine
tangents, at the upper \(c\) and the lower \(d\).

The exterior singleton \(cdLM\), floor \(d^4Z\),
geometry \(\min(d^3q,cC)J\), and highest prefix
\((1-d)(c-d)\max(v,n/2)\) enter the separate corner
bounds only. The interpolation is on the actual signed
exterior quantity and the common multiaffine physical
lower bound. The two exterior estimates each pay the
same crossing allowance. Their convex weights may vary
by corner. The accepted ratio sector still has one
common choice of \(f\) and both shifts on all four corners.
The ray blend and limiting-axis argument is unchanged.
All four corners are ordered since the code tests them
only when \(c_{\rm lo}\ge d_{\rm hi}\).

The discount \(d^2-(1-d)(c-d)=d-(1-d)c\) increases in
\(d\) and decreases in \(c\) on the rectangle, giving
the contractor's upper endpoint. The old residual
\(h/d<190\), \(k/d<11/2\), \(q/d<17\) gives the initial
upper limits \(143,33/8,51/4\) for \(d\le3/4\).
The already covered \(b\ge2d\) and \(q\le b/2\)
give the remaining lower cutoffs \(d\ge1/2,\ q\ge1/2\).
The two positive-shared inequalities and pure exterior
failure yield the implemented lower bounds on \(h,q,k\).
When \(1-q\) is negative the trivial \(k\ge0\) covers
the relevant inversion. All divisors in the remaining
contractor are positive. Slabs and child boxes cover their
closed boundaries using the previously audited outward
arithmetic. This review checks the source while the exact
traversal runs separately.
[Bilinear checker](../../verification/verify_rank7_fourth_tie_bilinear.cpp).
