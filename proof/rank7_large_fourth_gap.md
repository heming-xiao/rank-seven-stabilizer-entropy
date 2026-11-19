# Rank-seven optimality for a large fourth-to-fifth gap

November 18, 2026. Let the ordered positive Schmidt probabilities
be \((\alpha,\beta,\gamma,a,b,c,d)\). If
\[
                              7(a-b)\ge5d ,
\]
the sorted computational representative globally minimizes order-two
nonlocal stabilizer Rényi entropy on every qubit bipartition
over arbitrary complex local unitaries, with no restriction
on the other ordered ratios. At each fixed spectrum the argument
retains a positive paired-defect margin.
[Rank-seven equality and neighborhood transfer](rank7_all_tie_equalities.md).

Normalize \(d=1\). Write \(p=a-b\), \(q=\gamma-a\),
\(h=\alpha-\beta\), \(k=\beta-\gamma\), \(X=h+k+q\), \(Y=k+q\),
\(L=h+2k+3q\), \(g=hq\), \(\Delta=kX\).
Put \(D=1-p(a-c)-(b-1)(c-1)\).
The tied-middle theorem covers \(k=0\). The separated-bottom theorem
covers \(c\ge9/5\). If \(5g\le bL\) the small-shared theorem applies.
Thus only \(k>0,\ c<9/5,\ q>1/5\) need be considered, since
\(g\le qL\).
[Tied middle](rank7_equal_middle.md) ·
[Separated bottom pair](rank7_separated_bottom_pair.md) ·
[Small shared gain](rank7_small_shared_gain.md).

## A pure exterior comparison retaining all tail terms

Let \(n,v\) be the positive shared and highest-pair excesses,
\(M=\max(n,v/2)\), and \(P=\max(n,v)\).
The auxiliary four-head tie has shared deficit at least
\(2p^2(1-w_{0123})\), and highest-pair deficit at least
\[
 p(a-c)(1-w_{0123})+(b-1)(c-1)(2-I_4).
\]
Here \(1-w_{0123}\ge P\) and \(2-I_4\ge v\).
Use these prices in the signed exterior expansion with all mixed
shifts zero. The remaining completion term is \(XYqD_A\).
Since \(D_A\ge p(1-w_{0123})\) and \(Y\ge k\), this term
pays \(pq\Delta v\). The singleton terms separately pay
\(bcLM\). Together these distinct terms give
\[
 E\le\bigl[(c-2p^2)_+g+2(D-pq)_+\Delta-bcL\bigr]M .       \tag{1}
\]
Indeed the two positive excesses are bounded by \(M\) and
\(2M\), respectively, after replacing the residual coefficients by
their positive parts. [Signed expansion and weighted singleton prices](rank7_low_head_tail_prices.md) ·
[Shared loss](rank7_near_three_tails.md) ·
[Weighted highest-pair prefix](rank7_harmonic_tail_transport.md).

## Closing the spectrum comparison without a compression threshold

If the weighted highest-pair comparison at \(t=\Delta\) has strict
margin, the theorem already follows. Otherwise use its factor
\(\rho_t=6/7\), \(X\ge h\) and \(q+3a-b-c-1\ge0\).
The completion debit reduces the gain coefficient by at least
\(5pq/12\) in units of \(144\Delta\).
Writing \(J=122/25\) and \(B=7bc/6\), failure of strict margin implies
\[
 J\Delta^2\le 144\Delta\left(D-5pq/12-B/X\right).
\]
Here \(J\Delta^2\) comes from the highest-pair mixed and
anticommuting payment, using \(R\ge\Delta^2/5\).
In particular \(D-5pq/12>0\). Dividing by \(X\) and maximizing the
quadratic in \(1/X\) gives
\[
 k\le\frac{1800}{61}\frac{(D-5pq/12)^2}{4B}
       \le\frac{2700}{427}\,\frac{F(q)^2}{bc},
 \qquad F(q)=\frac{24}{49}-\frac{25}{84}q>0.              \tag{2}
\]
The last inequality uses \(D\le1-p^2\) and \(p\ge5/7\).
[Weighted residual](rank7_weighted_split_residual.md).

The sum of the positive terms of (1), divided by \(bcL\),
is at most
\[
 \frac{191}{441}q+
 13\left(\frac{24}{49}-\frac57q\right)_+ F(q)^2 .        \tag{3}
\]
The shared estimate uses \(c<9/5\) and \(g\le qL\), and the
highest-pair estimate uses \(\Delta\le kL\), (2),
\(2700/427<13/2\), and \(bc\ge1\).

For \(1/5\le q\le24/35\), the expression in (3) is convex because
its nonlinear term is a product of a nonnegative affine function
and the square of another, both decreasing. Its second derivative
is nonnegative by the product rule. The two endpoints are
strictly below one. For \(24/35\le q<288/175\), the highest-pair
term in (3) vanishes and its remaining linear term is also below
one. The upper endpoint \(288/175\) is the root of \(F\).
Thus (1) proves pure exterior optimality whenever the weighted
physical comparison alone had no strict margin. This completes
the whole claimed spectral family. [Exact rational constant checker](../verification/verify_rank7_large_fourth_gap.py).

