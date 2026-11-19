# Explicit bounds for the unresolved rank-seven spectra

November 18, 2026. For ordered probabilities
\((\alpha,\beta,\gamma,a,b,c,d)\), normalize \(d=1\) and write
\(h=\alpha-\beta\), \(k=\beta-\gamma\), \(q=\gamma-a\),
\(p=a-b\), \(g=hq\), \(\Delta=k(h+k+q)\).
The available sufficient comparisons confine every unresolved
spectrum to
\[
  101/100<c<2,\quad q>b/5,\quad p<1,\quad
  h<190,\quad b<21,\quad q+k<19,\quad \alpha<231 .
\]
In particular the bottom probability after normalizing by the
top probability is at least \(1/231\) on the closure of the
remaining domain. This is a sufficient-domain reduction.

The one-percent bottom-pair theorem gives \(c>101/100\).
The harmonic-mean tail theorem gives \(b(c-1)<c\), so \(c<2\).
Its highest-pair refinement requires
\((a-b)(a-c)+(b-1)(c-1)+pq/2<1\) in the remaining domain,
implying \(p<1\). The bounded middle-gap theorem gives \(q>b/5\).
[Bottom-pair theorem](rank7_near_two_tails.md) ·
[Middle-gap theorem](rank7_near_third_fourth.md) · [Tail transport](rank7_harmonic_tail_transport.md).

By the joint highest-pair criterion, equation (4), with its
nonnegative compression and supplemental payments dropped,
it remains to consider
\[
  J\Delta^2+\max\{g^2/24,q^4/72\}<144\Delta,\qquad
  J=(12+1/5)/(5/2)=122/25 .
\]
Indeed \(R\ge\Delta^2/5\), and the term
\(168kbc\) could also be retained with positive sign on the left.
Let \(u=144/(2J)=900/61\). The remaining inequality gives
\(0<\Delta<2u\) and
\[
  g^2<24J\bigl[u^2-(\Delta-u)^2\bigr],
  \qquad q^4<72Ju^2.
\]
In particular \(q<17\). [Joint criterion](rank7_leading_split_joint_payment.md) ·
[Independent verification of that criterion](reviews/rank7_highest_pair_round_independent_review.md).

By the pure exterior low-head test failure,
\(b<q+2k/c\). Thus \(b^2<(q+2k)^2\le q^2+4\Delta<21^2\) and
\((q+k)^2\le q^2+2\Delta<19^2\).
For the remaining top gap, set \(t=200/101>2/c\).
Then \(hb\le g+t\Delta\), since \(hk\le\Delta\).
Using the above bound on \(g\) and two-variable Cauchy–Schwarz gives
\[
 hb\le tu+
       t(\Delta-u)+
           \sqrt{24J}\sqrt{u^2-(\Delta-u)^2}
 \le u\bigl(t+\sqrt{t^2+24J}\bigr).
\]
The square root is less than \(1101/100\). As \(b>101/100\), we
obtain \(h<(100/101)u(t+1101/100)<190\).
Summing \(\alpha=h+k+q+p+b\) yields \(\alpha<231\).
[Low-head test](rank7_low_head_tail_prices.md) · [Rational parameter checks](../verification/verify_rank7_remaining_domain.py).

At each remaining spectrum the dimension-independent low-defect
threshold \(\delta(1/231)\) is therefore available. The next problem
is to prove the high-defect comparison in the indicated domain or
to find a physical frame achieving positive purity gain there.
[Low-defect theorem](rank7_low_defect_interior.md).

