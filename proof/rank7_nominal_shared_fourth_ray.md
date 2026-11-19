# Transferring a paid nominal shared interval off the fourth–fifth tie

November 18, 2026. Fix the ordered-tail data \(b,c,d>0\) and the
head gaps \(h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a\).
Along \(p=a-b\ge0\), all four leading weights grow together.
Consider a signed seed on \(a=b\) that uses the **nominal shared
interval**, pays its crossing allowance as in (1) below, and does not
use highest-pair compression. Suppose its other physical payments
remain available along the ray. The seed proves optimality for
every \(p\ge0\) whenever
\[
                         q\ge\max(b,11d/5).                    \tag{1a}
\]
The more general initial-data tests (5) below also suffice.
This covers the entire two-parameter family in the final section.

Write \(A=(101/100)168,\ X=h+k+q,\ Y=k+q,\ \Delta=kX,\ g=hq,\
S=cd,\ \alpha_0=b+X,\ \gamma_0=b+q\). The signed prices are
\(\lambda=24s/A,\ \mu=24t/A\) with
\(0\le s\le3g/2,\ 0\le t\le7\Delta/4\), zero triangle shift.
Let \(F(p)=E(p)-\lambda U(p)-\mu U_1(p)\). More precisely the seed
certificate, in the pertinent positive-excess frames, has the form
\[
 AF(0)+96D_\times(0)\le Q+96W(0)T_s,\qquad
 D_\times(0)=(\gamma_0hd/2)(b-c)w_{1234}.                     \tag{1}
\]
Here the actual signed higher-mode physical payment is at least \(Q\)
along the ray, \(W\) is the nominal squared width, and the chosen
trace lower price \(0\le T_s\le e=1-w_{0123}\) is available from
the shared cut on the same frame. For example the ratio-dependent
trace price in the [sixth-probability endpoint proof](rank7_positive_shared_tail_endpoints.md)
is at most \(n\le e\). The two axes use the existing paired comparison.
If the seed is restricted to positive exterior gain, \(E(p)>0\)
implies \(E(0)>0\) by the unpriced fourth-gap monotonicity.

## Changes of both the nominal width and the actual error

The two rows defining \(W\) are
\[
 W_A=\alpha c[\sqrt{d\gamma}-\sqrt{ba}]_+^2,\qquad
 W_B=\gamma c[\sqrt{d\alpha}-\sqrt{b\beta}]_+^2,\qquad
 W=\min(W_A,W_B).
\]
For \(f(u)=[\sqrt{d(u+v)}-\sqrt{bu}]_+^2\), the derivative bound
in the [true-cut transfer](rank7_true_cut_gap_ray.md) gives
\(-f'(u)\le d v^2/[4u(u+v)]\). Hence
\(-W_A'\le\alpha_0 S q^2/(4b\gamma_0)\). A positive active
\(W_B\) requires \(\beta\gamma\ge\alpha a\):
the two **nominal** outside scores are \(\alpha abc\) and
\(\beta\gamma bc\). This implies \(\gamma h\le\alpha q\).
Therefore
\[
 -W_B'\le\frac{\gamma S h^2}{4\beta\alpha}
          \le\frac{\alpha S q^2}{4\beta\gamma}
          \le\frac{\alpha_0S q^2}{4b\gamma_0}.
\]
The last bound uses that \(\alpha/\gamma\) decreases and
\(\beta\ge b\). Integrating the active derivative of the continuous
piecewise-smooth minimum proves
\[
             W(0)-W(p)\le \alpha_0 S q^2p/(4b\gamma_0).        \tag{2}
\]

The potentially entering wedges are \(123i,\ i=4,5,6\).
Let \(D_\times(p)\) denote their sum of actual per-wedge error
bounds in normalized compression units, including the wedge
variances. The general crossing estimate, with
\(w_I(1-w_I)\le w_I\), gives
\[
 D_\times(p)\le\frac{\gamma hd}{2}
 \left[p\sum_{i=4}^6 w_{123i}+(b-c)w_{1234}\right].
\]
The triple completion \(123\) gives \(\sum_{i=4}^6w_{123i}\le e\).
Subtracting the seed allowance in (1), with \(\gamma=\gamma_0+p\),
thus gives
\[
 D_\times(p)-D_\times(0)
           \le\tfrac12 hdp\,(\gamma_0+b-c+p)e.                 \tag{3}
\]
This compares the actual target errors to the **allowance purchased by
the seed**; a zero-error seed using only a true cut instead has the
separate actual-width transfer. [General crossing estimate](rank7_full_nominal_widths.md)

## Buying the difference once

The signed fourth-gap polynomial pays
\[
 A[F(0)-F(p)]\ \ge\ ep\{(A-78)\alpha_0Yq+2(A-36)gp\}.       \tag{4}
\]
In fact \(AC\ge(A-78)XYq\): the total normalized cubic price is
at most \(\max(2(3/2),3/2+7/4)=13/4\) in units of 24.
The unshifted triangle contributes \(AYq(3b-c-d)\ge AbYq\).
The coefficient \(2A(g-\lambda)\) covers \(2(A-36)g\) at degree
two. These are distinct terms of the unspent polynomial comparing the
actual signed gains at \(p\) and zero.
[Exact signed transport, equation (5)](rank7_fourth_third_product.md)

Consequently sufficient conditions are
\[
 \begin{aligned}
 (A-78)\alpha_0Yq &\ge
       24\alpha_0 S q^2/(b\gamma_0)+48hd(\gamma_0+b-c),\\
 2(A-36)g &\ge48hd .                                          \tag{5}
 \end{aligned}
\]
Indeed (2) times \(96T_s\), plus (3) times 96, is dominated by
(4). This transfers (1) to
\(AF(p)\le Q+96[W(p)T_s-D_\times(p)]\), a payable physical
comparison. For (1a) use \(S/(b\gamma_0)\le1,\ q\le Y,\
h\le\alpha_0,\ \gamma_0+b-c\le3q\).
The first inequality follows from \((A-102)Y\ge144d\);
the second follows directly from \(q\ge11d/5\).
The seed crossing is allocated once, even if its proof used a
convex combination of two alternative exterior estimates.

There is a wider criterion in the positive-shared remaining region.
When \(b\le2d,\ q\ge b/2\), one has \(2b-c\le3q\): for \(q\le d\)
use \(2b-c\le4q-d\), and for \(q\ge d\) use \(2b-c\le3d\).
Since \(S q/(b\gamma_0)\le d\) and \(h\le\alpha_0\), (5) then
holds as soon as
\[
                        Y=k+q\ge (33/14)d .
\]
Indeed the first price in (5), divided by \(\alpha_0q\), is at
most \(24d+192d\) and \((A-78)(33/14)>216\); the second price
is covered since \(q\ge d/2\). If \(q\ge b\), the same computation
uses \(24d+144d\), giving the alternative \(Y\ge11d/6\) with no
upper bound on \(b\). In particular (1a) can be replaced by the
single condition \(q\ge\max(b,11d/6)\).

## A positive-width rectangle of fourth and sixth probabilities

At \(d=1,\ b=11/10,\ (h,k,q)=(99/10,33/40,22/5)\) one obtains
global optimality for all \(1\le c\le11/10,\ p\ge0\).
The [existing endpoint seed](rank7_positive_shared_tail_endpoints.md)
for these gaps uses (1) and the shared compression without a highest
cut, with the shifts and ratio-dependent trace price described above.
Its remaining physical terms use \(h,k,q,b,c,d\) and the same frame.
In particular the direct shared matching correction \(200b(c-d)/11\)
and the rank-six correction with coefficient \(b(c-d)\) are valid
at arbitrary \(p\), and the lower anticommuting reserve used for their
convex allocation is independent of \(p\).
[General rank-six allocations](rank7_six_mode_joint_slacks.md)
Condition (1a) holds on the whole rectangle. This proves optimality
on all qubit cuts, with the paired margin inherited from the
strengthened comparison. The
[exact checker](../verification/verify_rank7_nominal_shared_fourth_ray.py)
verifies the completion row, the branch identity and constants.
