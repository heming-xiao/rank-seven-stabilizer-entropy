# Rank-seven optimality for a separated bottom pair

November 18, 2026. Every ordered positive rank-seven spectrum
\((\alpha,\beta,\gamma,a,b,c,d)\) satisfying
\[
                              5c\ge9d
\]
has order-two computational-basis optimality on arbitrary qubit
bipartitions and over arbitrary complex local unitaries. The other
five ordered probabilities are unrestricted. The proof uses a
same-frame mixed-residual comparison without compression terms.
It retains a positive paired-defect margin at every fixed positive
spectrum, so all optimizers form the sorted representative's local
Clifford orbit up to phase.
[Equality characterization](rank7_all_tie_equalities.md).

Normalize \(d=1\). For \(c\ge2\) the harmonic-tail theorem already
applies. Consider \(9/5\le c<2\). Use
\(h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a,\ p=a-b\),
\(X=h+k+q,\ \Delta=kX,\ g=hq\).
The case \(k=0\) is the tied-middle theorem.
For \(k>0\), put
\[
  D=1-p(a-c)-(b-1)(c-1),\qquad B=7bc/6,\qquad J=122/25.
\]
If the pure-exterior condition \(q+2k/c\le b\) applies, the
whole actual defect is retained.
[Harmonic-tail theorem](rank7_harmonic_tail_transport.md) ·
[Tied-middle theorem](rank7_equal_middle.md) ·
[Pure-exterior condition](rank7_low_head_tail_prices.md).

Otherwise \(q>b-2k/c\).
Suppose that the weighted residual comparison with \(t=\Delta\)
has no strict margin. Drop all nonnegative completion and
compression terms, and use \(R\ge\Delta^2/5\). Necessarily
\[
 J\Delta^2+\max(g^2/24,q^4/72)\le144\Delta\,m,\qquad
                  m=D-B/X>0 .
\]
The comparison \(D\le c(2-c)\le9/25\) uses \(b\ge c\ge9/5\),
and \(B\ge189/50\). Completing the square gives
\[
 \Delta\le (1800/61)m,\qquad g<160m,\qquad q<17\sqrt m .
\]
There is no bound on the head ratios in these estimates.
[Weighted residual proof](rank7_weighted_split_residual.md).

Using \(k=\Delta/X\) and the maximum of the quadratic
\(D/X-B/X^2\), we obtain
\[
 k\le\frac{1800}{61}\,\frac{D^2}{4B}<\frac{13}{50}.
\]
Hence \(q>9/5-2(13/50)/(9/5)>151/100\). Set \(r=151/100\).
Also \(X>B/D\ge21/2\). If \(X\le12\), then
\(m\le9/25-(189/50)/12\) gives \(q<4\).
If \(X\ge12\), then \(q<17\sqrt{9/25}=51/5\).
In both cases \(q+r<X-k\). Therefore
\[
   g=q(X-k-q)\ \ge\ r(X-k-r)>r(X-13/50-r),
\]
since \(q(X-k-q)-r(X-k-r)=(q-r)(X-k-q-r)\ge0\).
Combining with \(g<160(D-B/X)\) would force
\[
 2\sqrt{160\,r(189/50)}
 \ \le\ rX+160B/X\
 <\ 160(9/25)+r(13/50+r).
\]
The two positive sides have the reverse strict order by squaring.
This contradicts failure of the weighted residual test. Its strict
margin also supplies the stated equality and per-spectrum
neighborhood. [Exact rational constant check](../verification/verify_rank7_separated_bottom_pair.py).


## A separate unbounded region with a large fifth probability

The same weighted transfer proves global optimality whenever \(b\ge9d\),
regardless of \(c\) and of all four higher probabilities. The proof
uses the known remaining-domain reduction and the small-shared
theorem. It gives a strict paired margin and the same optimizer
classification at every fixed spectrum.
[Remaining-domain reduction](rank7_remaining_domain.md) ·
[Small-shared theorem](rank7_small_shared_gain.md).

Again put \(d=1\). It is enough to consider \(9\le b<21\),
\(k>0\), where the pure exterior and small-shared conditions fail.
Suppose the same weighted residual comparison at \(t=\Delta\)
has no strict margin. Write \(D,B,J,m\) as above. Then \(D\le1\),
\(B\ge7b/6\), \(g<160m\), and \(q<17\). Completing the square
using \(\Delta\le(1800/61)m\) gives
\[
       k\le\frac{1800}{61}\frac{D^2}{4B}
                          <\frac{13}{2b}.
\]
Failure of the pure exterior condition gives \(q>b-2k/c>
b-13/b>2b/3\). Failure of the small-shared test gives
\[
       h(5q-b)>3bq,\qquad q<17\le2b,
\]
so \(h>2b/3\) also. For \(s=2b/3\) the product
\((h-s)(q-s)\) is nonnegative, whence \(g\ge s(X-k-s)\).
Combining with the upper bound for \(g\) and applying AM–GM
gives the incompatible demands
\[
 \frac{223}{10}b
 <2\sqrt{160sB}
 \ \le\ sX+160B/X
 <160+s(k+s)
 <160+13/3+4b^2/9 .
\]
Indeed the difference of the two outer bounds in the other order
is a concave quadratic in \(b\), with positive values at \(9\) and
\(21\). The exact constant check verifies both endpoints.

