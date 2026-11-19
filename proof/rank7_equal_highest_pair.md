# Rank-seven computational-basis optimality with the two largest probabilities equal

November 18, 2026. Let the Schmidt rank be seven and suppose the
probabilities are proportional to \((1,1,r,t,a,b,s)\), where
\(1\ge r\ge t\ge a\ge b\ge s>0\). The sorted computational-basis
representative globally minimizes the order-two nonlocal stabilizer
Rényi entropy on its local-unitary orbit for every qubit bipartition.
Each such spectrum also has a full relative open neighborhood of
rank-seven spectra with the same conclusion, including spectra whose
seven probabilities are distinct.

Fix a physical orthonormal frame. Let \(E\) be the normalized
four-exterior overlap difference from the sorted reference and
\(U_1\) the highest-pair weighted difference. If \(U_1\le0\), apply
the [highest-pair cubic bound](rank7_highest_pair_split_loss.md).
For leading probabilities \(\alpha=\beta=1\) and third \(\gamma=r\),
the spectrum obtained by reducing both highest probabilities by
\(k=1-r\) is \((r,r,r,t,a,b,s)\). The three largest probabilities
of this spectrum are equal, so both exceptional prices in the
[forward-gap comparison](rank7_forward_coefficients_independent.md)
are zero. Its exterior difference \(E_0\) is therefore nonpositive
for the same frame. The new bound gives
\[
 E\le E_0+(1-r)(1-t)U_1\le0 .
\]
The rank-seven exterior compression and the purity defect inequality
then give the desired single-unitary comparison, retaining the whole
Pauli defect.

If \(U_1>0\), use the earlier
[weighted positive-branch proof](rank7_tied_head_positive_branch.md).
Its spectral coefficient is \(\Gamma=1-r-t-a-b+s\).
For \(\Gamma\le0\) its weighted packing estimate gives \(E\le0\).
For \(\Gamma>0\) the mixed-sector defect and exterior compression
cover the gain with a positive spectral coefficient margin.
That proof uses an analytic inequality for \(s<2/21\) and two
exact rational Bernstein certificates for \(s\ge2/21\).
These certify the full positive-branch range when the five tail
probabilities are strictly ordered or have ties. Crucially, the
cubic bound covers the negative-\(U_1\) frames without any
condition on the sign of \(\Gamma\).

For a fixed spectrum in the positive branch, let \(A\) be the
gain coefficient and \(B>A\) the certified payment coefficient,
both multiplying the same \(U_1>0\). A spectrum-dependent positive
fraction of the actual payment remains after comparison with the
gain, since \(A/B<1\). On all other branches the entire defect is
retained. The [strict-margin transfer](rank7_open_interior_neighborhood.md)
gives the full relative open neighborhoods, and the paired
Cauchy–Schwarz and stabilizer-padding reductions give every cut.

[Independent combined review](reviews/rank7_highest_pair_round_independent_review.md) · [Original purity reduction and compression theorem](https://arxiv.org/html/2609.13106v2)
