# The shared nominal compression width at rank seven

The shared nominal interval is inactive exactly when
\(\alpha d\le\beta b\) or \(\gamma d\le ab\). Its lower endpoint
squared is \(\max(\alpha abc,\beta\gamma bc)\). The distinct highest
interval is inactive exactly when \(\beta d\le\gamma b\).
[Definitions of the two intervals](rank7_crossed_compression.md)

Every positive ordered rank-seven spectrum satisfying
\[
                 \boxed{\ \alpha d\le\beta b\quad\text{or}\quad\gamma d\le ab\ }
\]
has sorted computational optimality on every qubit cut. All four
larger probabilities may be distinct and the highest nominal interval
may be active. This settles the entire zero-shared-nominal-width
region; the other spectral regions do not enter this statement.

## The alternative lower endpoint

Use the same two exterior estimates, disjoint physical payments
and symbols \(z=h/b,\ y=k/b,\ x=q/b,\ D,\ S,T,\theta,K_0,A\)
as in the [three-variable reduction](rank7_zero_nominal_payment.md).
Normalize \(d=1\). The earlier results give \(1\le b\le3\),
\(p=a-b<5/7,\ c\le\min(9/5,b)\) on the remaining domain.
On a fixed rational slab \(b_\ell\le b\le b_u\), the assumption
\(\gamma\le ab\) is equivalent to \(x\le(b-1)(1+p/b)\).
It gives
\[
 B=\max\{b_\ell,1+x/(1+5/(7b_\ell))\}\le b,\qquad
 0\le p_* = B[x/(b_u-1)-1]_+\le p .
\]
The first line of the prior estimate (2) retains the auxiliary
highest-pair deficit with coefficient \(\Delta-\mu\);
that deficit is at least \(p(a-c)(1-w_{0123})\ge p^2v\).
This term is separate from the singleton and floor terms.
The second line uses \(U_1\le(1-p^2)v-qD_A\), by the same
prefix inequality. Hence the factor multiplying \(D\) on the
right in each of tests (4),(5) may be multiplied by
\((1-p_*^2)_+\). In the first test replace \(2/9\) by
\(2/b_u^2\) and the bound \(c\le9/5\) by
\(c\le\min(9/5,b_u)\). All replacements are conservative.
[Highest-pair deficit](rank7_harmonic_tail_transport.md) ·
[Distinct singleton and prefix deductions](rank7_large_fourth_gap.md)

The remaining box for \((z,y,x)\) is
\([3/5,190]\times[0,11/2]\times[1/5,17]\). The larger first
endpoint uses \(h<190\), since this branch imposes no upper head
ratio. The [standard-library checker](../verification/verify_rank7_zero_shared_width.py)
partitions \(b\in[1,3]\) into 16 slabs of width \(1/8\).
In addition to the domain exclusions of the two-ratio proof it
applies the [head-gap theorem](rank7_large_fifth_probability.md)
when \(x\le1/2\) or \(z\le3/2\) throughout a box, and
\(B^2(z+4y+3x)\ge22\). That test implies
\(bc(h+4k+3q)\ge22\), since \(c\ge1\).
Running the command below verified **27,835 leaves** and reached
maximum depth 29. It proves this branch including both signs of \(H\).

~~~text
python verification/verify_rank7_zero_shared_width.py tail
~~~

## The upper-head ratio

For \(\alpha\le\beta b\) the separate lower bound is
\[
 B=\max\{b_\ell,1+z/(1+x+y+5/(7b_\ell))\}\le b .
\]
If desired the bound
\(p\ge B[z/(b_u-1)-1-x-y]_+\) gives the same highest discount.
These formulas follow by writing \(h\le(b-1)\beta\) with
\(\beta=b(1+x+y)+p\). Here \(z\le2(1+x+y+5/7)<50\)
on the remaining domain, so the smaller initial box from the
two-leading-ratio proof applies. Two exact traversals independently
exhausted the upper-head branch:

| Command suffix | Slabs | Accepted leaves | Maximum depth |
| --- | ---: | ---: | ---: |
| head | 4 | 646,826 | 34 |
| head-fine | 16 | 304,954 | 33 |

The four broad slabs have endpoints \(1,5/4,3/2,2,3\); their
counts in order are \(3984,13516,613686,15640\). This version
sets the auxiliary lower bound on \(p\) to zero and uses no
head-gap exclusion. The fine version uses the same 16 slabs as
the tail test together with the optional \(p\) discount and
head-gap exclusion above. Run either:

~~~text
python verification/verify_rank7_zero_shared_width.py head
python verification/verify_rank7_zero_shared_width.py head-fine
~~~

The checker's SHA-256 for all three commands is
\(\texttt{bab74ca254c035b3e7f5a8b549332ff5c6e864b36389a3229e520fc9c5284a31}\).
Its file dependency is the frozen two-ratio checker, with the
corresponding hash recorded in the [two-ratio proof](rank7_zero_nominal_payment.md).
