# One exterior compression cut closes a second strictly ordered regression

November 18, 2026. For every ordered positive Schmidt spectrum proportional to
\[
 (19.32,4.69,4.13,1.012,1.008,1.004,1),
 \tag{1}
\]
where the terminating decimals are exact, the sorted computational-basis
representative globally minimizes the order-two nonlocal stabilizer Rényi
entropy over arbitrary complex local unitaries and every qubit bipartition.
Every such spectrum has a full relative open neighborhood of optimality.

The certificate adds a single threshold of the actual four-wedge compression
to one simultaneous mixed-probe bound and the independent anticommuting
defect. Two linear duals have altogether 45 nonzero prices drawn from the
original 98 unconditional physical packing rows. The proof uses a strict
factor \(21/20\) on the exterior gain. [Exact verifier](../verification/verify_rank7_joint_single_cut_regression.py) · [Two stored rational duals](../certificates/rank7/rank7_joint_single_cut_regression.json)

## Signed prices for the actual defects

Use \((\alpha,\beta,\gamma,a,b,c,d)\) for (1) and set
\[
 h=\alpha-\beta,\quad k=\beta-\gamma,\quad q=\gamma-a,\quad
 g=hq,\quad \Delta=k(\alpha-a),\quad
 R=k^2[k^2+(h^2+q^2)/2],\quad G=g-\tfrac{200}{11}b(c-d)>0 .
\]
Let \(E\) be the normalized linear exterior gain, \(U_1\) the weighted
highest-pair occupancy difference from the reference, and \(U=U_1+U_2\)
the weighted difference for pairs \(01,02\). Put \(v=L_{01}-2\) and
\(\nu=L_{01}+L_{02}-4\). Define
\[
 P=24G U+24\Delta U_1+
       \tfrac{12G^2+g^2}{12}\nu+
       \tfrac{12\Delta^2+R}{5/2}v .
 \tag{2}
\]

The simultaneous mixed bound may use shifts \(G,\Delta\), because the shared
and highest-pair probes include the respective reciprocal cross prices
\(\Delta c_1,gc_1\). The resulting cross remainder \(24\Delta g c_1\) is
nonnegative. The choice of \(G\) follows from the six-mode occupation bound
on both the small- and large-defect branches. The retained mixed price is
\(24G U+24\Delta U_1+12G^2\kappa+12\Delta^2\kappa_1\). The actual
anticommuting defect independently supplies \(g^2\kappa+R\kappa_1\).
Using \(\kappa\ge\nu/12\), \(\kappa_1\ge v/(5/2)\) in the resulting
positive coefficients gives (2) as a lower bound on their sum.
These signed inequalities hold even when one of the two excesses is negative.
[Joint mixed shifts and anticommuting prices](rank7_leading_split_joint_payment.md) · [Shared geometry](rank7_shared_anchor_twelve_and_anticommuting.md) · [Highest-pair geometry](rank7_highest_pair_geometry_five_halves.md)

## A single trace and two unconditional packing duals

Let \(\mathcal C\) consist of all wedges containing label \(0\) and at
least one label from \(\{1,2\}\). Set \(s=\sum_{I\in\mathcal C}w_I\).
At the computational frame \(s_*=3\). The following are affine inequalities
for every nonnegative occupancy vector satisfying the 98 rows:
\[
 \begin{aligned}
 E+200(s-18/5)&\le -5224003751/781250000,\\
 (21/20)168E &\le P+768(s-3).
 \end{aligned}
 \tag{3}
\]
The verifier reconstructs the cost of every wedge for the two inequalities.
For example the cost contributing to \(U_1\) is zero outside \(01\) and the
product of the two remaining probabilities inside \(01\). It checks that
the 22 and 23 nonnegative row prices, respectively, cover all 35 columns
and yield the claimed objectives.

In the increasing order of the squared exterior amplitudes, the cut
\(\mathcal C\) begins at index 19 (index zero is the smallest).
The smallest squared amplitude inside is the score of wedge \(0256\);
the largest outside is that of wedge \(0345\). The gap
\(\sigma=\sqrt{\alpha\gamma cd}-\sqrt{\alpha abc}\) satisfies
\(\sigma^2>20\); the verifier checks this by two rational sign comparisons
and squaring. The compression loss on every actual frame therefore obeys
\(\mathcal D_F\ge \sigma^2\phi(s)\), with
\(\phi(s)=\{s\}(1-\{s\})\). This follows either by cutting the
spectral compression identity into the two blocks, or by keeping this one
term of the nested threshold inequality. [Spectral compression identity](rank7_compression_slack_astra.md)

For \(E>0\), the first dual gives \(s<18/5\). If \(3\le s<18/5\),
then \(\phi(s)\ge(2/5)(s-3)\); if \(s<3\), the right side is nonpositive.
Consequently \(96\mathcal D_F\ge768(s-3)\) throughout the positive-gain
branch. The second inequality of (3) covers \((21/20)168E\) with the sum
of the distinct actual defects. This retains at least \(1/21\) of their
total on that branch. When \(E\le0\) the entire defect is available.
The one-frame purity inequality, two-frame Cauchy–Schwarz transfer,
stabilizer padding and strict-margin transfer prove the claims at (1).
[Reduction and neighborhood transfer](rank7_open_interior_neighborhood.md)

## Test of the compression estimate alone

The verifier also constructs a rational array with all weights in
sixths, checks the 98 packing rows and all 21 pair bounds \(L_{ij}\le7/3\),
and rigorously bounds from above the complete standard sum of 35
adjacent-gap rounding terms. For this array, that sum falls short of
\((7/4)E\) by more than 14 in normalized compression units. This tests
the sufficiency of the nested lower estimate. Physical realizability
of the array is unnecessary. The combined proof (2)–(3) covers every
physical frame, including any frame that could have those occupancies.

