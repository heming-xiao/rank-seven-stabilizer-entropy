# Rank-seven optimality with a bounded third-to-fourth gap

November 18, 2026. For every ordered positive rank-seven Schmidt
spectrum \((\alpha,\beta,\gamma,a,b,c,d)\) satisfying
\[
                         5(\gamma-a)\le b ,
\]
the sorted computational representative globally minimizes order-two
nonlocal stabilizer Rényi entropy over every complex local-unitary
orbit, on any qubit bipartition. The other ratios are unrestricted.
The proof retains at least \(1/101\) of the actual paired defect.
All optimizers are the local Clifford images of the sorted
representative up to phase, including at tied spectra and at the
endpoint of the inequality.
[Paired transfer and open neighborhoods](rank7_open_interior_neighborhood.md) ·
[Rank-seven equality characterization](rank7_all_tie_equalities.md).

## Absorbing the shared gain in the singleton deficit

Set \(d=1\), \(h=\alpha-\beta\), \(k=\beta-\gamma\),
\(q=\gamma-a\), \(p=a-b\), \(X=h+k+q\), \(Y=k+q\),
\(g=hq\), \(\Delta=kX\), \(L=h+2k+3q\),
and \(R=k^2(k^2+(h^2+q^2)/2)\).
Use the notation \(E,U_1,n,v,P,M\) from the
[signed exterior comparison](rank7_low_head_tail_prices.md), taking
both \(n\) and \(v\) to be positive parts here.
Let \(A=(101/100)168\), \(\mu=30\Delta/A\), and \(\rho=1-30/A\).
In its three-probe comparison set the shared and triangle probe
charges to zero. The cubic completion coefficient is nonnegative
because \(XYq-\mu q\ge0\). The highest-pair deficit is at least
\(p^2(1-w_{0123})\ge p^2v\) and the constant deficit is at least
\(2v\), as in the [exact middle-tie proof](rank7_equal_third_fourth.md).

The ordering and \(q\le b/5\) give the bound
\[
                   cgn\le \tfrac15 bc\, hM .
\]
Consequently the entire shared gain fits within one fifth of the
weighted singleton price \(bcLM\). The remaining four fifths pay
at least \((4/5)bcLv/2\). The mixed shift \(t=5\Delta/4\) and the
independent anticommuting estimate, after retaining only the
highest-pair sector, pay
\(24tU_1+[(45/4)\Delta^2+R]v/(5/2)\).
Subtracting \(AE\) then gives the lower bound \(AvB\), where
\[
 B=2+\frac{(4/5)bcL}{2}+\rho\Delta p^2-\rho\Delta+
   \frac{(45/4)\Delta^2+R}{(5/2)A}.
\]
The expression is sufficient whenever \(v=0\) as well, since the
entire subtracted payment is then nonnegative without a compression
cut. The trace margin is only used on positive exterior gain.
[Highest-pair mixed shift](rank7_two_probe_separation_and_tail_region.md) ·
[Independent anticommuting payment](rank7_two_probe_anticommuting.md).

## Two analytic outer regions

Let \(x=\Delta\) and \(J=(45/4+1/5)/[(5/2)A]\).
The anticommuting estimate gives \(R\ge x^2/5\).
The debit from \(\rho x-Jx^2\) is bounded by \(\rho^2/(4J)\).
Thus \(L\ge13\) suffices, since \(bc\ge1\) and
\(2+(4/5)(13/2)>\rho^2/(4J)\).

If \(a+b+c\ge4\), then \(p+2(b-1)+(c-1)\ge1\), so
\(bc\ge1+(b-1)+(c-1)\ge(3-p)/2\).
Also \(L/2\ge\sqrt x\) by
\((h/2+k+3q/2)^2-k(h+k+q)\ge0\).
Writing \(m=4/5\), we obtain
\[
 \begin{aligned}
 B&\ge 2+\tfrac32m\sqrt x-\tfrac12mp\sqrt x+\rho xp^2-\rho x+Jx^2\\
  &\ge 2-\tfrac{m^2}{16\rho}+\tfrac32m\sqrt x-\rho x+Jx^2 .
 \end{aligned}
\]
For \(x\in[0,9]\), \([9,16]\), and \([16,\infty)\) use respectively
\(\sqrt x\ge x/3\), \(\sqrt x\ge(x+12)/7\), and
\(\sqrt x\ge4\). In every case the resulting quadratic has a
strictly positive minimum over the whole real axis. These three
rational comparisons are checked by the exact verifier.

## One exact compression cut on the compact region

Only \(h+2k<13\) and \(p+2(b-c)+3(c-1)<1\) need subdivision.
The highest-pair wedge family has inside minimum score
\(\alpha\beta c\) and outside maximum score \(\alpha\gamma ab\).
Its single separated threshold pays at least
\[
                    32v\alpha\frac{(\beta c-\gamma ab)^2}{
                                              \beta c+\gamma ab}
\]
when the numerator's score gap \(\beta c-\gamma ab\) is
nonnegative. This is the same trace estimate as in the middle-tie
proof, now retaining the true third probability \(\gamma\).
Use zero when the threshold is unseparated.
[Nested compression](rank7_compression_slack_astra.md).

Substitute
\[
 (h,k,p,b-c,c-1)=(13u_1,(13/2)u_2,u_3,u_4/2,u_5/3),
 \qquad q=(b/5)u_6,
\]
with all six coordinates in \([0,1]\).
A leaf proves \(B\ge0\), or both \(\beta c-\gamma ab\ge0\) and
\[
 (\beta c+\gamma ab)B+(32/A)\alpha(\beta c-\gamma ab)^2\ge0 .
\]
Nonnegative exact Bernstein coefficients verify each applicable
comparison, or the lower corner certifies one of the two
analytic branches. The exact six-variable tree has 456 base leaves,
223 cut leaves and 32 outer leaves, with maximum depth 20.
[Exact verifier](../verification/verify_rank7_equal_third_fourth.py).

All branches pay \(AE\) entirely from the actual mixed,
anticommuting and compression losses on positive exterior gain.
On nonpositive exterior gain the full defect remains. Rescaling
and the paired reduction give the theorem.

