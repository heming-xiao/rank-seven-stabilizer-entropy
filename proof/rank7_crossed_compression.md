# Four-exterior compression across spectral crossings at rank seven

November 18, 2026. Two simultaneous compression prices remain
available when the highest-pair or shared-pair wedge set fails to be
an upper spectral cut. The first comparison keeps the entire widths
of two specified amplitude intervals, with a correction supported on
six nonreference wedges. A second comparison gives a positive joint
highest-pair price at every spectrum in the [remaining domain](rank7_remaining_domain.md),
including exact collisions between a highest-pair product and another
product. Its exterior terms must be allocated from the existing proof;
it does not by itself prove the full rank-seven conjecture.

Write \(A_I=\sqrt{\prod_{i\in I}t_i}\), where
\(t=(\alpha,\beta,\gamma,a,b,c,d)\) are ordered positive
probabilities up to scale. Let \(0\le T\le I\) be the normalized
four-wedge compression and \(w_I=T_{II}\). The exact loss on one
physical frame is
\[
 {\cal D}_F=\sum_I A_I^2(T-T^2)_{II}
               +\sum_{I<J}(A_I-A_J)^2|T_{IJ}|^2.
\]
For a coordinate projection \(R\) define
\(F_R=\operatorname{Tr}[(RTR)(I_R-RTR)]\) on its range. Then
\(F_R=\sum_{I\in R}(T-T^2)_{II}
+\sum_{I\in R,J\notin R}|T_{IJ}|^2
\ge\phi(\sum_{I\in R}w_I)\), where
\(\phi(x)=\{x\}(1-\{x\})\).
[Compression identity and trace rounding](rank7_compression_slack_astra.md)

## Two full nominal widths and six possible crossing wedges

Take \(R_1=\{01\subset I\}\) and \(R_s=\{0\in I,\ I\cap\{1,2\}\ne\varnothing\}\).
Define squared endpoints
\[
 u_1^2=\alpha\beta cd,\quad l_1^2=\alpha\gamma bc,\qquad
 u_s^2=\alpha\gamma cd,\quad l_s^2=\max(\alpha abc,\beta\gamma bc).
\]
For \(j=1,s\) put \(s_j=(u_j-l_j)_+^2\) and
\(r_j(z)=[s_j-(u_j-z)_+^2]_+\).
The complementary errors are supported on
\(H_1=\{023i,123i: i=4,5,6\}\) and
\(H_s=\{123i:i=4,5,6\}\). On every frame,
\[
 \boxed{\displaystyle
 {\cal D}_F\ge s_1 F_{R_1}+s_s F_{R_s}
 -\sum_{j\in\{1,s\}}\sum_{I\in H_j}
                  r_j(A_I)\,w_I(1-w_I).} \tag{1}
\]
In particular each \(F_R\) may be replaced by its rounded trace.
No true separation at either cut is required.

Every inside amplitude is at least its \(u_j\), and every outside
amplitude above \(l_j\) must be in the indicated \(H_j\), by sorting
the four labels. The two active intervals have disjoint interiors
because \(u_s\le l_1\). For a pair of wedges separated by one or
both cuts, let \(I\) denote the inside wedge for every cut involved;
these directions agree by nesting. Let \(J\) be the outside wedge.
The amount \(s_j-r_j(A_J)\) is the square of the length of
\([l_j,u_j]\cap[A_J,A_I]\), taking zero when \(A_J>A_I\) or the
interval is inactive. The sum of these squared lengths is at most
\((A_I-A_J)^2\). The diagonal non-projection terms pay their full
assigned \(s_j\), since the disjoint intervals for an inside wedge
lie in \([0,A_I]\). Finally each outside wedge \(J\) is charged at
most \(r_j(A_J)\sum_{I\ne J}|T_{IJ}|^2
\le r_j(A_J)w_J(1-w_J)\) per cut. This proves (1) without cutting
a nominal width into separate squared subintervals.
[Earlier subinterval construction on three equal tails](rank7_fourth_gap_lift.md)

There is also a spectrum-only price on that error. Put
\[
 M_i=w_{023i}+w_{123i},\quad e=1-w_{0123},\quad
 D_A=a-\sum_{i=3}^6t_iw_{012i},\quad p=a-b .
\]
The two triple-completion bounds give \(\sum_{i=4}^6M_i\le2e\).
The complement \(56\) row gives
\(M_4\le1-w_{0123}-w_{0124}\). Writing
\(x=1-\sum_{i=3}^6w_{012i}\) yields
\[
 D_A=p e+b x+(b-c)w_{0125}+(b-d)w_{0126}
              \ge pe+(b-c)M_4. \tag{2}
\]
Set
\[
 R_i=\max\{r_1(A_{023i}),\
          r_1(A_{123i})+r_s(A_{123i})\},\quad i=4,5.
\]
The errors are increasing in the outside amplitude, so \(R_4\ge R_5\)
and the price at label 6 is at most \(R_5\). The error in (1) is
at most \(2R_5 e+(R_4-R_5)M_4\), hence at most \(K D_A\) for
\[
 K=\max\{2R_5/p,\ (R_4-R_5)/(b-c)\}.
\]
If \(p=0\) the two errors at label 5 vanish; if \(b=c\) the two
label prices coincide. A vanishing numerator and denominator are
assigned ratio zero. Thus any available price \(C\ge0\) in the
same units as \({\cal D}_F\) gives
\[
 {\cal D}_F+C D_A\ge
 \min(1,C/K)\,[s_1F_{R_1}+s_sF_{R_s}], \tag{3}
\]
with full multiplier when \(K=0\). In a physical purity comparison
charging \(A_* E\) and supplying \(96{\cal D}_F\), an exterior
coefficient \(C_{\rm ext}\) on \(D_A\) gives
\(C=A_*C_{\rm ext}/96\). Only the share of \(C_{\rm ext}\) set
aside for (3) is available here.

## A highest-pair width at every spectrum in the remaining domain

Let \(I_4=\sum_{01\subset I,\,6\notin I}w_I,\ N=\operatorname{Tr}T\).
Consider these two sets of protected wedges:
\[
 \begin{split}
 {\cal G}_{11}={}&\{0123,0145,2345\}
       \cup\{\{i,j\}\cup\{k,l\}: ij\in\{02,03,12,13\},
                                   kl\in\{46,56\}\},\\
 {\cal G}_{19}={}&\bigcup_{\pi\in S_{\{3,4,5\}}}\pi({\cal G}_{11}).
 \end{split}
\]
The second consists of the six highest-pair wedges avoiding 6,
the twelve wedges with exactly one of \(0,1\), label 6, and two
of \(2,3,4,5\), and the single wedge \(2345\).
For \(W_j=\sum_{I\notin{\cal G}_j}w_I\) the unconditional
98 physical rows imply
\[
 W_{11}\le\tfrac34(7-N)+4e+4(2-I_4),\qquad
 W_{19}\le\tfrac54(7-N)+4(2-I_4). \tag{4}
\]
The [standard-library verifier](../verification/verify_rank7_crossed_compression.py)
lists the nonnegative rational prices and verifies both exact
reference totals and all 70 column inequalities. In particular
the face \(N=7,\ I_4=2\) is supported on the 19 wedges, and
\(w_{0123}=1\) restricts it further to the 11 wedges.

In either protected set the lowest inside amplitude is
\(u=\sqrt{\alpha\beta bc}\). The largest protected outside values are
\[
 l_{11}=\sqrt{\gamma b\max(\alpha d,ac)},\qquad
 l_{19}=\sqrt{\gamma a\max(\alpha d,bc)}.
\]
The respective maxima are over wedges \(0246,2345\) and
\(0236,2345\). Define \(s_j=(u-l_j)_+^2\). For either choice,
\[
 {\cal D}_F\ge s_j\big[F_{R_1}
                -\sum_{I\notin{\cal G}_j}w_I(1-w_I)\big]
        \ \ge\ s_j[\phi(L_{01})-W_j]. \tag{5}
\]
Indeed a protected inside wedge pays the full \(s_j\) on its
non-projection term and on every cross entry to a protected
outside wedge. For an unprotected inside wedge, its non-projection
term and all its cross entries sum to at most \(w_I(1-w_I)\).
An unprotected outside wedge is charged only cross entries coming
from protected inside wedges and obeys the same bound.
This covers every remaining term exactly once.

For a quantitative exterior allocation, take nonnegative available
coefficients \(A_N,A_e,A_4\) on \(7-N,e,2-I_4\), in the units
of \({\cal D}_F\). Then (4) and (5) give
\[
 {\cal D}_F+A_N(7-N)+A_e e+A_4(2-I_4)\ge s\,\phi(L_{01}),
 \tag{6}
\]
with either
\[
 s=\min(s_{11},4A_N/3,A_e/4,A_4/4),\qquad
 s=\min(s_{19},4A_N/5,A_4/4).
\]
On positive highest-pair excess, \(\phi(L_{01})\ge(2/3)(L_{01}-2)\).
In the [signed exterior expansion](rank7_three_price_head_expansion.md),
for any \(\lambda,\mu\) leaving \(C>0,\ \mu<\Delta\), the
three quantities can be allocated from \(d^4(7-N), Cpe\),
and \((\Delta-\mu)(b-d)(c-d)(2-I_4)\), respectively. The last
source is the [five-tail weighted prefix loss](rank7_harmonic_tail_transport.md).
Any desired positive fraction can be assigned, converting units as
in (3) and retaining the balance for other terms. For example take
the shared and highest shifts with \(0\le\lambda\le g/7,\ \mu=\Delta/7\);
the completion coefficient is then positive for \(X,Y,q>0\).

In the remaining domain \(c>d,\ q>0,\ k>0\). If \(p>0\), then all
three allocations above are positive, and \(s_{11}>0\) because
\(\beta c>\gamma d\) and \(\alpha\beta>\gamma a\). If \(p=0\),
then \(l_{19}=l_{11}\), and the second price requires only the
first and third allocations. Thus (6) indeed supplies a positive
joint rate at every remaining point, without testing distinctness
of the 35 products. It is an exterior-plus-compression inequality.
In both protected sets all retained inside wedges avoid 6, so
\(W_j\ge L_{01}-I_4\ge(L_{01}-2)_+\). The scalar lower bound
\(s_j[\phi(L_{01})-W_j]\) alone therefore cannot force positive
compression on positive excess. Reusing the exterior allocations
of (6) in another scalar payment would double-count them. The
six-outside-wedge inequality (1) instead protects **all** inside
wedges and does not incur this particular loss.

## A genuine double crossing on a physical frame

Take \((8,5,3,8/5,3/2,6/5,1)\). Both usual upper-set tests
fail strictly: \(u_1^2=48<\alpha\gamma ab\) and
\(u_s^2=144/5<\beta\gamma ab\). However \(l_1^2=216/5\)
and \(l_s^2=27\). Using
\((x-y)^2/[2(x+y)]\le(\sqrt x-\sqrt y)^2\le(x-y)^2/(4y)\)
for \(x\ge y>0\) gives
\[
       1/8<s_1\le2/15,\qquad 1/35<s_s\le3/100.
\]
In four physical qubits take mode 3 to be
\((|3\rangle+|8\rangle)/\sqrt2\), with the other six modes
at their computational labels. A quadruple with label 8 and
three other labels below 7 cannot sum to zero in binary.
Consequently the four reference planes incident to mode 3 have
half their original occupancy, the other three retain one, and
all other wedges have zero occupancy. In particular all six
crossing wedges have zero occupancy, \(L_{01}=3/2\) and
\(\operatorname{Tr}R_sT=5/2\). From (1),
\[
                          {\cal D}_F>43/1120 .
\]
The strict nominal widths and the failure of both true-cut tests
persist on an open set of fully ordered spectra about this point.
This physical example improves the compression lower bound directly;
its exterior gain is nonpositive and it is not a counterexample to
computational-basis optimality.

## An all-frame regression with an improved strict scalar margin

At the fully ordered rational spectrum
\[
              (22.7,\ 8.075,\ 7.68,\ 1.8221,\ 1.822,\ 1.725,\ 1)
                                                               \tag{7}
\]
formula (3) pays the full nominal shared width on every frame and
proves global sorted-computational optimality on every qubit cut,
with at least \(1/101\) of the actual defect sum retained.
The same holds on an open neighborhood. In the comparison below
the usual separated cuts give a negative scalar margin on at least
one direction even after retaining their completion and geometric
credits. This compares these particular sufficient scalar tests;
it does not rule out other independent proofs at (7).

Use \(d=1,\ A_*=(101/100)168,\ h=\alpha-\beta,\ k=\beta-\gamma,\
q=\gamma-a,\ p=a-b,\ X=\alpha-a,\ Y=\beta-a,\ g=hq,\
\Delta=kX,\ J=Yq,\ L=h+2k+3q,\ R=k^2[k^2+(h^2+q^2)/2]\).
Take the improved shared coefficient
\[
 G=\big[g-(200/11)\{b(c-1)-(\gamma-c)p\}_+\big]_+.
\]
The shared and highest mixed shifts are \(5G/4,5\Delta/4\);
put \(\lambda=30G/A_*,\ \mu=30\Delta/A_*,\
C=XYq-\lambda(Y+q)-\mu q\).
The mixed cross coefficient
\((5\Delta/4)g-(5G/4)\Delta/4\) is nonnegative.
When the untruncated matching coefficient is negative, the shared
shift is zero, so truncating it in this scalar formula is valid.
[Tail-corrected shared matching](rank7_triangle_probe_tail_equalization.md) ·
[Two simultaneous shifts](rank7_four_equal_tails.md)

Write \(n=\nu_+,\ v=(L_{01}-2)_+,\ P=\max(n,v),\
M=\max(n,v/2),\ Z=\max(5n/2,2v,2n+v)\).
With the completion \(C D_A\) entirely set aside, the lower bound
on the non-compression payment minus \(A_*E\), divided by \(A_*\)
and omitting this reserved term, is
\[
\begin{split}
 B={}&bcLM+Z-c(g-\lambda)n-(\Delta-\mu)v\\
 &+P\left[\frac{g^2+(45/4)G^2}{12A_*}+p^4+Lp^3
             +p^2\{2(g-\lambda)+(\Delta-\mu)+3J\}\right]\\
 &+\frac{(45/4)\Delta^2+R}{(5/2)A_*}\,v .
\end{split} \tag{8}
\]
Here \(p^4+Lp^3\) and the three \(p^2\) terms are separate
wedge losses. The \(bcLM\) and \(Z\) credits use the ordinary
singleton and total occupancy rows; none uses \(D_A\).
[General unequal-tail wedge losses](rank7_near_three_tails.md)

At (7), the nominal highest width is zero. For the shared width
write \(u=u_s^2,\ l=l_s^2=\beta\gamma bc,\ l'=\beta\gamma ab\);
the usual separated width uses \(l'\), where \(l<l'<u\).
Since \(r_s(z)\) is \(2\sqrt{s_s}\)-Lipschitz in \(z\), the error
coefficient \(K\) in (3) satisfies
\[
 K\le\max\left\{\frac{4\sqrt{s_s}\sqrt{\beta\gamma c}}{\sqrt a+\sqrt b},
                 \frac{2\sqrt{s_s}\sqrt{\beta\gamma a}}{\sqrt b+\sqrt c}
          \right\}<96 .
\]
The first quotient uses
\(A_{1235}-l_s=\sqrt{\beta\gamma c}(\sqrt a-\sqrt b)\).
The second uses
\(A_{1234}-A_{1235}=\sqrt{\beta\gamma a}(\sqrt b-\sqrt c)\).
The verifier checks \(\sqrt{s_s}<4\), both spectral square roots
below 12, and \(96^2<A_* C\). Thus the reserved completion pays
**the whole** crossing cost. On \(E>0\), the existing trace theorem gives
\(\phi(\operatorname{Tr}R_sT)\ge\omega n\), with
\(\omega=(aXYq-\Delta/3)_+/(cg+2aXYq)\).
All six ray directions satisfy the exact comparison
\[
                    B+\frac{96\omega n}{A_*}
                          \frac{(u-l)^2}{2(u+l)}>3/10 .
\]
These rational margins apply at the six normalized directions;
homogeneity and linearity on their intervening sectors give the
physical inequality for all \(n,v\). At \(n=v=0\) the unsigned
exterior bound suffices. [Shared trace price](rank7_uniform_cut_packing.md)

For the parallel separated-cut test the verifier gives it back
\(CpP+q(2n+v-3M)_+\) (the latter is admissible since
\(9XY\ge14\)) and uses the true squared width
\((\sqrt u-\sqrt{l'})^2\), rounded upwards in its favor using an
integer square root. Its minimum over the same six rays is less
than \(-3/20\). The strict new margins, strict crossing-price
budget and strict product order persist on a neighborhood of (7).
The full defect comparison, local Clifford equality classification,
and two-frame transfer then follow as in the
[three-equal-tail proof](rank7_three_equal_tails.md).
[Exact rational regression](../verification/verify_rank7_crossed_compression.py)


