# Rank-seven optimality when the third and fourth probabilities coincide

November 18, 2026. For every ordered positive spectrum proportional to
\((\alpha,\beta,a,a,b,c,d)\), on every qubit bipartition the sorted
computational representative globally minimizes order-two nonlocal
stabilizer Rényi entropy over arbitrary complex local unitaries.
The other eigenvalues have arbitrary ordered ratios. The paired purity
comparison retains at least \(1/101\) of the actual defect, giving a
full neighborhood at each such spectrum. All minimizing states form
the sorted representative's local Clifford orbit up to phase.

## One highest-pair comparison

Normalize \(d=1\). Set \(h=\alpha-\beta\), \(k=\beta-a\),
\(p=a-b\), \(L=h+2k\), \(\Delta=k(h+k)\), and
\(R=k^2(k^2+h^2/2)\). The shared head gap \(g=h(\gamma-a)\)
and the cubic completion coefficient vanish. Write \(v=L_{01}-2\)
for the signed highest-pair excess, \(E\) for the normalized exterior
gain, and \(U_1\) for the weighted highest-pair probe difference.
The forward price gives \(E\le\Delta v\), so a positive exterior gain
requires \(\Delta>0\) and \(v>0\).
[Forward price](rank7_forward_coefficients_independent.md).

Put \(A=(101/100)168\), \(t=5\Delta/4\),
\(\mu=24t/A\), and \(\rho=1-30/A\). The single mixed shift and the
independent anticommuting sector pay \(24tU_1\) plus
\([(45/4)\Delta^2+R]\kappa_1\), with \(\kappa_1\ge v/(5/2)\).
Take the shared and triangle shifts zero in the signed exterior
comparison. The highest-pair deficit \(B_1\) at the tied-four-head
auxiliary spectrum is at least \(p^2(1-w_{0123})\ge p^2v\):
the first two tail weights of that probe are \(a,a\), and the
length-two prefix squared has gap factor \(p^2\).
The singleton price is \(bcLM\), with \(M\ge v/2\), and the
constant coefficient gives \(N-7\le-2v\). These are distinct terms
in the signed exterior comparison. Thus
\[
 E-\mu U_1\le
 \bigl[\rho\Delta(1-p^2)-bcL/2-2\bigr]v.
\]
[Single shift](rank7_two_probe_separation_and_tail_region.md) ·
[Anticommuting sector](rank7_two_probe_anticommuting.md) ·
[Signed exterior price and singleton term](rank7_low_head_tail_prices.md) ·
[Highest-pair prefix](rank7_near_three_tails.md) ·
[Constant price and compression normalization](rank7_uniform_cut_packing.md).

After division of the payments by \(Av\), it suffices to cover the
following scalar, with the compression loss still available:
\[
 B=bcL/2+2+\rho\Delta p^2-\rho\Delta+
   \frac{(45/4)\Delta^2+R}{(5/2)A}.
\]
Here \(B\) is the available payment minus the gain. Complete the
square using \(R\ge\Delta^2/3\), which follows from
\((h+k)^2\le3(h^2/2+k^2)\). The total debit from the linear term
is strictly below \(7\), while \(bcL/2+2\ge7\) when \(L\ge10\).
This handles the unbounded head regime.

## An analytic comparison for larger tails

If \(a+b+c\ge4\), use the signed spectral floor bound directly:
\[
 E\le Fv,\qquad
 F=\Delta-(h/2+k)(b+c-1)-2(a+b+c-2).
\]
Independently \(E\le\Delta U_1\), by lowering the highest two
probabilities together until the top three increments have no
contributing quadratic head gap. More precisely the partner is
\((\alpha-k,a,a,a,b,c,1)\); its exterior gain is nonpositive,
and the highest-pair split bound gives the displayed comparison.
Use the convex combination with weight \(30/A\) on the latter
bound. The \(U_1\) term now cancels the mixed shift, leaving only
\(\rho Fv\). [Signed floor](rank7_spectral_floor_single_probe.md) ·
[Highest-pair split](rank7_highest_pair_split_loss.md).

Since \(h/2+k\ge\sqrt\Delta\), we have
\(F\le\Delta-\sqrt{\Delta}-4\). The normalized quadratic
payment divided by \(\rho\) is at least
\(\Delta^2(45/4+1/3)/[(5/2)A\rho]>\Delta^2/31\).
For \(x\ge0\), \(x-\sqrt x-x^2/31<4\): on \([0,9]\) use
\(\sqrt x\ge x/3\) and the increasing quadratic with its
endpoint \(105/31\). On \([9,16]\) the chord gives
\(\sqrt x\ge(x+12)/7\), bounding the result by \(195/49\).
On \([16,\infty)\) use \(\sqrt x\ge4\) and
\(x-x^2/31\le31/4\). This proves the same strict factor in the
large-tail branch without using compression.

## Exact compact comparison with one compression threshold

For \(L\le10\) and \(a+b+c\le4\), write
\(r=b-c\), \(s=c-1\). The inequalities imply
\(h/10+k/5\le1\) and \(p+2r+3s\le1\).
On the highest-pair wedge family the smallest
squared amplitude is \(\alpha\beta c\), and outside that family
the largest is \(\alpha a^2 b\).
If the squared-amplitude difference is nonnegative,
the single separated threshold pays at least
\[
 64v(\sqrt{\alpha\beta c}-\sqrt{\alpha a^2 b})^2
 \ \ge\
 32v\alpha\,\frac{(\beta c-a^2b)^2}{\beta c+a^2b}.
\]
There is no charge when their order is reversed. The trace
coefficient \(64v\) follows from \(L_{01}\le7/3\), so the fractional
trace at this cut gives \(v(1-v)\ge 2v/3\), multiplied by \(96\).
Equality of the gap can be included by continuity.
[Nested compression](rank7_compression_slack_astra.md) ·
[Highest-pair trace cap](rank7_uniform_cut_packing.md).

The standard-library exact verifier substitutes
\((h,k,p,r,s)=(10u_1,5u_2,u_3,u_4/2,u_5/3)\) into \(B\).
It proves either \(B\ge0\) on a dyadic box or both
\[
 \beta c-a^2 b\ge0,\qquad
 (\beta c+a^2b) B+(32/A)\alpha(\beta c-a^2b)^2\ge0 .
\]
Boxes whose lower corners certify either outer branch are
excluded by the analytic proofs. All remaining boxes pass with
nonnegative integer-scaled Bernstein coefficients. The tree has
26 base leaves, six cut leaves and five outer leaves, with
maximum depth 11. The independent reconstruction used a different axis
priority and half-interval formula, and passed with 47 base leaves,
eight cut leaves and seven outer leaves, with maximum depth 12.
[Exact verifier](../verification/verify_rank7_equal_third_fourth.py).

Every branch on \(E>0\) pays \(A E\) from the mixed,
anticommuting and compression defect sum. On \(E\le0\) the full
defect is retained. The paired Cauchy–Schwarz comparison and
stabilizer padding give unrestricted physical optimality on
every qubit cut. A zero Pauli defect forces stabilizer-basis
diagonal marginals, so the rank-seven equality result gives the
Clifford characterization, also for repeated probabilities.
[Strict transfer](rank7_open_interior_neighborhood.md) ·
[Equality with ties](rank7_all_tie_equalities.md).

## A uniform positive separation of the middle pair

This same global comparison and equality characterization hold when
\[
 0\le(\gamma-a)/d\le
 \frac{\delta(1/1057)}{404\cdot19208\cdot33}.
\]
Outside \(\alpha/d<1057\) the known exterior or large-length
comparison retains a strict margin. Inside it normalize by
\(\alpha\), set \(\gamma\) to \(a\) to define the reference partner,
and keep the same seven-frame. Both spectra have bottom probability
at least \(1/1057\). For actual normalized Pauli defect
\(\eta\le\delta(1/1057)\), the low-defect theorem gives
nonpositive exterior gain. Otherwise the Lipschitz defect bound
\(5376\) retains at least \(\eta/2\) at the partner. Its margin
\(\eta/202\) exceeds the comparison change by at least
\(\eta/404\), using the Lipschitz bound
\(19208\sqrt{1057}<19208\cdot33\).
[Compact reduction](rank7_compact_remaining_spectra.md) ·
[Low-defect cutoff](rank7_low_defect_interior.md) ·
[Lipschitz estimates](rank7_open_interior_neighborhood.md).


The direct [bounded middle-gap comparison](rank7_near_third_fourth.md) gives the wider bound \(5(\gamma-a)\le b\) and keeps a \(1/101\) margin.
