# Transport of a true highest cut and a paid nominal shared cut

November 18, 2026. Fix ordered positive tails \(b\ge c\ge d\) and
nonnegative \(h,k,q\). Write
\[
 p=a-b,\quad \gamma=a+q,\quad \beta=\gamma+k,\quad \alpha=\beta+h,
 \quad Y=k+q,\quad X=h+Y,\quad g=hq,\quad \Delta=kX .
\]
For **every \(q\ge 2d/3\)**, a paired seed at \(p=0\) of the form (1)
below proves the same signed physical comparison at every \(p\ge0\).
The seed may simultaneously use the true highest width and the
nominal shared width. All \(b/d,k/d,h/d\) are allowed.
Together with the [unconditional small-third-gap theorem](rank7_low_third_gap.md),
this removes \(p\) from the remaining problem whenever the initial
comparison provides the specified receipt. That initial comparison is
a hypothesis.

## The seed and the physical payment

Use \(A=(101/100)168,\ S=cd,\ \alpha_0=b+X,\ \gamma_0=b+q\).
Fix \(0\le s\le3g/2,\ 0\le t\le7\Delta/4\), set
\(\lambda=24s/A,\ \mu=24t/A\), and take zero triangle shift.
Write \(F=E-\lambda U-\mu U_1\), using the actual signed exterior
and the two actual weighted gains on the fixed frame. The assumed
comparison at the tie is
\[
 AF(0)+96D_0\le Q+96[W_1(0)T_1+W_s(0)T_s],\qquad
 D_0=\tfrac d2(b-c)\min(\gamma_0h,\alpha_0q)
                         w_{1234}(1-w_{1234}).                \tag{1}
\]
Any larger previously purchased allowance also suffices; this includes
\(\gamma_0hd(b-c)w_{1234}/2\).
Here \(Q\) remains payable after restoring the signed charges at
every point of this ray. The frame, shifts and selected trace prices
\(T_1,T_s\) are fixed for the transfer. Each may depend on the frame.
The prices must be lower bounds for the respective available
compression traces and satisfy \(0\le T_1,T_s\le e=1-w_{0123}\).
In particular when the two raw excesses \(v,n\) are positive,
the actual rounded traces have this upper bound. A smaller multiple
of either excess can also be used whenever it bounds the trace at
both ends. If (1) is only assumed on \(E(0)>0\), the unshifted
fourth-gap monotonicity gives \(E(0)\ge E(p)\). Nonpositive gain
and the other excess sectors have the existing paired comparison.
[Trace bounds and axes](rank7_true_cut_gap_ray.md)

The widths are
\[
\begin{split}
 W_1&=\alpha[\sqrt{\beta cd}-\sqrt{\gamma ab}]_+^2,\\
 W_s&=\min(W_A,W_B),\\
 W_A&=\alpha c[\sqrt{d\gamma}-\sqrt{ab}]_+^2,\qquad
 W_B=\gamma c[\sqrt{d\alpha}-\sqrt{b\beta}]_+^2 .
\end{split}
\]
The true highest interval has lower endpoint \(\sqrt{\alpha\gamma ab}\).
The shared interval has upper endpoint \(u=\sqrt{\alpha\gamma cd}\)
and lower endpoint \(l=\max(\sqrt{\alpha abc},\sqrt{\beta\gamma bc})\).
Since \(ab\ge cd\), the intervals have disjoint interiors when both
are active. The physical four-wedge loss supplies
\[
 W_1T_1+W_sT_s-D_\times(p),\quad
 D_\times(p)=\sum_{i=4}^6 r(z_i)w_{123i}(1-w_{123i}),
 \quad r(z)=[(u-l)_+^2-(u-z)_+^2]_+,
\]
where \(z_i=\sqrt{\beta\gamma a r_i}\), \((r_4,r_5,r_6)=(b,c,d)\).
For an entry crossing one or both nested projections, the squares
of the lengths of the disjoint intervals intersected with its
amplitude gap sum to at most that gap squared. The first interval
is an actual cut. The second incurs the displayed three errors,
using the total off-diagonal squared mass in each offending row
at most \(w_{123i}(1-w_{123i})\). The diagonal nonprojection
terms cover their assigned intervals by the same disjointness.
[Crossed compression identity](rank7_crossed_compression.md)

## A two-sided bound for each entering shared wedge

Put \(B_4=p+b-c,\ B_5=B_6=p\). At every spectrum one has
\[
             r(z_i)\le \tfrac d2\min(\gamma h,\alpha q) B_i .
                                                               \tag{2}
\]
The \(\gamma h\) bound holds for all three wedges by the
[full-width crossing estimate](rank7_full_nominal_widths.md).
For the other bound the inactive interval is immediate. If \(W_B\)
controls the positive minimum, then \(\beta\gamma\ge\alpha a\),
so \(\gamma h-\alpha q=\alpha a-\beta\gamma\le0\).

If \(W_A\) controls, then \(\beta\gamma\le\alpha a\). Since
\(l\ge\sqrt{\alpha abc},\sqrt{\beta\gamma bc}\), use the first
outside endpoint for the interval width and the second for the
crossing overshoot. This gives
\[
 r(z_i)\le2(u-l)_+(z_i-l)_+
 \le2\sqrt{\alpha c}\,[\sqrt{d\gamma}-\sqrt{ab}]_+
    \sqrt{\beta\gamma}\,[\sqrt{a r_i}-\sqrt{bc}]_+ .
\]
The last positive part is at most \(\sqrt{b}B_i/(2\sqrt c)\).
For \(i=4\) factor out \(\sqrt b\) and rationalize
\(\sqrt a-\sqrt c\). For \(i=5,6\) use
\(\sqrt c(\sqrt a-\sqrt b)\le \sqrt c\,p/(2\sqrt b)\).
Also \(d\gamma-ab=dq-(b-d)a\le dq\), so the first positive
part is at most \(dq/(2\sqrt{ab})\). Combining gives
\(r(z_i)\le (dq/2)\sqrt{\alpha\beta\gamma/a}\,B_i
\le (\alpha dq/2)B_i\), proving (2).

Use the \(\alpha q\) price for the common \(p\) in (2), and write
\(m(p)=\min(\gamma h,\alpha q)\) for the price of the additional
\(b-c\) at label four. One has \(m(p)-m(0)\le hp\). If \(h\ge q\)
both affine branches have slope at most \(h\). If \(h<q\), the
minimum is \(\gamma h\) throughout because \(\gamma\le\alpha\).
The triple-completion row \(123\) gives \(\sum_{i=4}^6w_{123i}\le e\).
Retaining the fourth variance when subtracting \(D_0\) and using
\(\alpha=\alpha_0+p\) gives
\[
 D_\times(p)-D_0\le
       \tfrac{dp}{2}[\alpha_0q+pq+h(b-c)]e.                  \tag{3}
\]
Only the allowance explicitly purchased in (1) is subtracted.

## Paying all changes from one signed polynomial

The two integrated width bounds on this ray are
\[
 W_1(0)-W_1(p)\le p\,\alpha_0\zeta(S/b)k,\qquad
 W_s(0)-W_s(p)\le p\,\alpha_0(S/b)q^2/(4\gamma_0),
 \quad \zeta=4-2\sqrt3 .
\]
The first uses the actual highest outside endpoint. The second
uses the active branch of the nominal minimum and permits switches.
[True highest slope, (3)](rank7_true_cut_gap_ray.md) ·
[Nominal shared slope, (2)](rank7_nominal_shared_fourth_ray.md)

The signed fourth-gap polynomial supplies the lower bound
\[
 A[F(0)-F(p)]\ge ep\{
   (A-78)\alpha_0Yq+(A-36)hq(b-c)+3AYq\,p\}.               \tag{4}
\]
Indeed, the cubic coefficient is
\(C=XYq-\lambda(Y+q)-\mu q\) and \(AC\ge(A-78)XYq\).
For \(XYq>0\) divide the debit by \(24XYq\). It is at most
\((3/2)(h/X)(1+q/Y)+(7/4)(1-q/Y)\le13/4\).
The distinct triangle contribution linear in \(p\) is
\(AYq(3b-c-d)\ge AbYq\). Together these give the first term
of (4). The second uses the shared linear contribution
\(A(g-\lambda)(2b-c-d)\ge (A-36)hq(b-c)\).
The last is the quadratic triangle term, available in full.
[Signed fourth-gap polynomial, (5)](rank7_fourth_third_product.md)

After multiplication by 96 the last two terms of (3) are paid by
the last two terms of (4), because \((A-36)q\ge48d\) and
\(3AY\ge48d\). The remaining budget pays both width decreases
and the leading term of (3) provided
\[
 (A-78)(k+q)q
 \ \ge\ 96\zeta(S/b)k+48dq+24(S/b)q^2/(b+q).               \tag{5}
\]
Use \(S/b\le d\). The coefficient of \(k\) is covered by
\((A-78)q\ge96\zeta d\), since at \(q=2d/3\) the left-hand side
is \(1528d/25\), whereas \(\zeta<27/50\).
For the other terms one needs
\((A-78)q\ge48d+24d q/(b+q)\). At \(q=2d/3\) the right side
is at most \(288d/5\) using \(b\ge d\). Its derivative in \(q\)
is at most \(24\), while \(A-78>24\). This proves (5) on the
entire stated ray. The comparison includes \(p=0,\ e=0\)
and vanishing \(h\) or \(k\).

Together (3)–(5) show that the right side of (4) dominates
\(96[(W_1(0)-W_1(p))T_1+(W_s(0)-W_s(p))T_s+D_\times(p)-D_0]\).
Consequently (1) implies the desired physical comparison
\[
 AF(p)\le Q+96[W_1(p)T_1+W_s(p)T_s-D_\times(p)] .
\]
The [exact checker](../verification/verify_rank7_mixed_cut_full_fourth_ray.py)
checks the branch and polynomial identities, the completion row,
and the rational rate comparisons.
