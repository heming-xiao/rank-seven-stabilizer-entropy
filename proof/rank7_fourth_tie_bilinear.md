# A two-tail corner certificate at a fourth–fifth tie

Normalize \(a=b=1\), with the remaining tail probabilities
\(d\le c\le1\). Hold \(h=\alpha-\beta,\ k=\beta-\gamma,\
q=\gamma-a\) fixed. Put \(X=h+k+q,\ Y=k+q,\ L=h+2k+3q,\
g=hq,\ \Delta=kX\), and \(A=4242/25\).
The exact candidate covers \(1/2\le d\le3/4\). This is disjoint
from the independent small-fifth checker below \(b/d=4/3\)
apart from their common endpoint.

## The corrected exterior gain at the four corners

For a fixed frame let \(n,v\) be the two positive leading
excesses. Let \(M=\max(n,v/2),\ P=\max(n,v),\
Z=\max(5n/2,2v,2n+v),\ J=(2n+v-3M)_+,\
B=\max(v,n/2)\). For shifts \(0\le s\le3g/2\) and
\(0\le t\le7\Delta/4\), take \(\lambda=24s/A,\ \mu=24t/A\),
\(C=XYq-\lambda(Y+q)-\mu q\), and \(H=g-h-3q-5/2\).
Then \(C\ge0\) and the shared/highest cross payment is
nonnegative.

On the residual domain \(q\ge1/2\), the signed singleton
and the tied-middle split each cover the nominal shared
crossing \(D_\times=\gamma h d(1-c)w_{1234}/2\). This is
the homogeneous form of the [sixth-probability endpoint
comparison](rank7_positive_shared_tail_endpoints.md). For
the signed gain with its crossing allowance,
\[
               F=E-\lambda U-\mu U_1+96D_\times/A,
\]
the two alternative upper bounds are
\[
\begin{aligned}
 cd(g-\lambda)n&+(\Delta-\mu)
 [d^2v-(1-d)(c-d)B]\\
 &\quad-cdLM-d^4Z-\min(d^3q,cC)J,\\
 cd(H-\lambda)n&+(\Delta-\mu)
 [d^2v-(1-d)(c-d)B]-kcdv .
\end{aligned}
\]
The signed singleton estimate uses the auxiliary shared
deficit for the crossing. The split uses its retained
shared and completion deficits together. The separate
highest prefix discount remains available in both bounds.
The two bounds are combined convexly, so the same
crossing allowance enters once.
[Full shared width after either exterior bound](rank7_positive_shared_tail_endpoints.md) ·
[Highest prefix discount](rank7_harmonic_tail_transport.md).

The actual \(F\) is multiaffine in \(c,d\) on the same physical
frame, meaning affine in either variable with the other held
fixed. The monomials in the gain and weighted differences
contain each tail entry at most once. The additional
crossing allowance is proportional to \(d(1-c)\).
The nonlinear upper bounds above are evaluated only at
the four corners. It is the actual \(F\) and a common
multiaffine lower price that are interpolated.

## A common multiaffine physical lower price

Let \([c_\ell,c_u]\times[d_\ell,d_u]\) be a tail rectangle
whose corners all satisfy \(d\le c\le1\).
Use a fraction \(f\) of the rank-six mixed estimate and
\(1-f\) of the direct estimate. Put
\(\Lambda=(1-f)200/11\) and use a fixed lower bound \(\Psi_0\)
on
\[
        \Psi=(c-d)^2+\{h^2+q^2+(1-c)^2+d^2\}/6 .
\]
The global tail portion is at least \(1/13\), since the
three nonnegative gaps \(c-d,\ 1-c,\ d\) sum to one and
weighted Cauchy–Schwarz uses reciprocal weights \(1,6,6\).
A larger interval lower bound comes from
\((c_\ell-d_u)_+^2+[(1-c_u)^2+d_\ell^2]/6\).
Use the larger of these two bounds and add \((h^2+q^2)/6\).
The rank-six mixed correction then uses
\(Q=1+12 f^2/\Psi_0\). Take
\[
 g_0=(g-\Lambda(c_u-d_\ell))_+,\qquad s=u g_0/Q,\qquad t=w\Delta .
\]
The chosen \(u,w\) are fixed across all four corners, and
\(g_0,Q\) also remain fixed on the tail rectangle at
any fixed head spectrum. The shared quadratic payment is
bounded below by
\[
  12u(2-u)g_0^2/Q+24s\Lambda[(c_u-d_\ell)-(c-d)].
\]
The formula is valid also when \(g_0=0\), as then \(s=0\).
It is nonnegative and affine in \(c,d\). The independent
leading anti contributions are \(g^2\kappa+R\kappa_1\),
and the highest mixed price is \(12t(2\Delta-t)\kappa_1\).
The separate odd reserve replaces \((1-c)^2+d^2\) by
its affine lower tangent
\((1-c_u)(1+c_u-2c)+d_\ell(2d-d_\ell)\).
Each term of this tangent is nonnegative on the box.
The rank-six cost uses only the \(P_6,P_6\) and odd-to-\(P_6\)
slots, separate from the leading and odd reserve prices.
[Conditional mixed and tail slots](rank7_positive_shared_tail_endpoints.md) ·
[Odd-to-leading slots](rank7_triangle_probe_tail_equalization.md).

For the true highest interval let
\(u_1=\alpha\beta cd,\ell_1=\alpha\gamma\).
For the nominal shared interval let
\(u_s=\alpha\gamma cd,\ell_s=c\max(\alpha,\beta\gamma)\).
The actual highest outside endpoint is at least the
shared inside endpoint, so the intervals are disjoint.
Only the shared interval has an entering-wedge error.
For any fixed \(z\ge0\) use the width lower price
\[
           z(u_i-\ell_i)-z^2(u_i+\ell_i)/2 .
\]
This is multiaffine in \(c,d\). The choice of \(z\) is a
rational lower bound on \((u_i-\ell_i)_+/(u_i+\ell_i)\)
at the lower-left corner. The maximizing ratio is
nondecreasing in \(cd\) for the highest interval and
in \(d\) for the shared interval, since the latter
has a common factor \(c\). Consequently each lower
price is nonnegative throughout the rectangle.
[Disjoint intervals](rank7_crossed_compression.md) ·
[Joint trace prices](rank7_joint_trace_prices.md).

## Verification and transfer

The directed-integer [checker](../verification/verify_rank7_fourth_tie_bilinear.cpp)
uses one \(s,t,f\) on an adjacent pair of ratio rays
throughout the four corners. Each corner may select
its own convex exterior weight, provided it works on
both boundary rays. The seven rays suffice by the
concavity of the two trace prices within each ratio
sector and the affine-plus-increasing function on the
last unbounded sector. Interpolating the actual \(F\)
and the physical lower price proves the comparison on
the entire rectangle. Boxes intersecting the unordered
corner \(c<d\) are subdivided to keep the interpolation
in the ordered domain. The existing close-bottom
theorem covers sufficiently small boxes next to \(c=d\).

The coordinate contractor uses the maximum possible
\(D_0=d-(1-d)c\) in the rectangle. Any unresolved actual
spectrum satisfies \(g<160D_0,\ \Delta<(1800/61)D_0\)
in the tie normalization before increasing \(p\).
The active shared inequalities give
\(q>1/d-1,\ h>(1/d-1)(1+k+q)\). The low-head bound gives
\(q+2dk/c>1\). Every clipping direction is outward.
[Independent source review](reviews/rank7_c_affine_highest_and_bilinear_independent_review.md).

The exact first slab \(d\in[1/2,9/16]\) completed
6,455,151 leaves at depth at most 39. The computation
accepted further leaves in its second slab, but the
old execution session no longer exists and the second
slab's completion has not been verified.
The completed slab's source SHA-256 is
\( \texttt{b54915b451858b9cf6b095d52d001ce8cd9b95844fd28942ef0845b8976d0af3} \).
The imported source SHA-256 is recorded in the
[lower-fifth note](rank7_tied_fourth_lower_fifth.md).

The \([1/2,9/16]\) slab therefore proves every spectrum
with \(16d/9\le b\le2d\), including arbitrary \(a-b\).
The mixed branch supplies a paid nominal shared and
actual highest certificate. The weighted branches
use \(t\le3\Delta/2\) in the range \(b/d\ge4/3\).
The branch-by-branch proof then transmits the whole
verified cover to the actual spectrum with \(p\ge0\).
The earlier \(b\ge2d\) theorem completes the unbounded
region \(b\ge16d/9\).
[All branch transfers](rank7_seed_branch_transfer.md) ·
[Mixed-cut ray](rank7_mixed_cut_full_fourth_ray.md).


## Restartable subintervals

The CLI now accepts the exact requested interval as three integers
`lower upper denominator`. With no arguments it still uses the
original slab boundaries. No comparison, contraction, or bisection
rule changed. The CLI build was compiled cleanly with `-Wall -Wextra`
and passed the following fully recorded runs.

| \(d/b\) interval | Accepted leaves | Depth | Log |
| --- | ---: | ---: | --- |
| \([144/256,145/256]\) | 2,884,075 | 37 | [Run](../certificates/rank7/upper_fifth_144_145_of_256.log) |
| \([145/256,148/256]\) | 4,004,520 | 37 | [Run](../certificates/rank7/upper_fifth_145_148_of_256.log) |
| \([148/256,152/256]\) | 9,491,102 | 40 | [Run](../certificates/rank7/upper_fifth_148_152_of_256.log) |
| \([152/256,156/256]\) | 9,789,024 | 40 | [Run](../certificates/rank7/upper_fifth_152_156_of_256.log) |
| \([156/256,160/256]\) | 13,857,356 | 40 | [Run](../certificates/rank7/upper_fifth_156_160_of_256.log) |
| \([160/256,164/256]\) | 5,548,191 | 39 | [Run](../certificates/rank7/upper_fifth_160_164_of_256.log) |
| \([164/256,168/256]\) | 17,385,523 | 41 | [Run](../certificates/rank7/upper_fifth_164_168_of_256.log) |
| \([168/256,172/256]\) | 17,456,883 | 41 | [Run](../certificates/rank7/upper_fifth_168_172_of_256.log) |
| \([172/256,176/256]\) | 14,895,902 | 40 | [Run](../certificates/rank7/upper_fifth_172_176_of_256.log) |
| \([176/256,180/256]\) | 11,200,130 | 40 | [Run](../certificates/rank7/upper_fifth_176_180_of_256.log) |
| \([180/256,184/256]\) | 5,474,944 | 37 | [Run](../certificates/rank7/upper_fifth_180_184_of_256.log) |
| \([184/256,188/256]\) | 6,843,026 | 37 | [Run](../certificates/rank7/upper_fifth_184_188_of_256.log) |
| \([188/256,192/256]\) | 8,554,105 | 37 | [Run](../certificates/rank7/upper_fifth_188_192_of_256.log) |

All listed logs record exit code zero. The CLI source SHA-256 is
`ffd06e81b72842e64752b9c3f62f73344e39a60d70cd73f3fc2dcf311bca66d5`.
The contiguous upper region now starts at \(b/d=4/3\).
The two completed lanes covered the disjoint cells with lower numerators
148, 156, 164, 172, 180, 188 and 152, 160, 168, 176, 184,
respectively, each of length \(4/256\). Only logs with a `Completed slab`
line and `exit 0` certify a completed cell. Valid completed cells can
be kept even if their execution session has ended. To resume a missing
cell, compile the same source and pass its own two numerators and 256.
