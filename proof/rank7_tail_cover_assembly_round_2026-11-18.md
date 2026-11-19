# Full Schmidt-rank-seven computational-basis optimality

The preceding [round record](rank7_seed_transfer_and_priority_round_2026-11-18.md)
contains the directed-interval reductions and the independent reviews.
Let \(\xi=d/b\), where \(b\) and \(d\) are the fifth and seventh
Schmidt probabilities in decreasing order. The target is order-two
stabilizer Rényi entropy over the full complex local-unitary orbit of
every pure state with Schmidt rank seven, on every qubit bipartition.

**Theorem.** For any qubit bipartition and any pure state of
Schmidt rank seven, its descending computational-basis Schmidt
representative attains the minimum of order-two stabilizer Rényi
entropy on the orbit under arbitrary complex local unitaries.

The proof uses exact directed-integer interval arithmetic after
reducing the purity comparison to a dimension-independent family
of paired-frame inequalities. The thirteen cells that close the
last ratio band passed with 127,384,781 accepted leaves. All cells
include their rational endpoints.

## From paired frames to the local orbit

On a balanced cut of local dimension \(D\), use the coefficient
matrix \(T=U_A M U_B^{\mathsf T}\), with \(M\) diagonal and equal
to the sorted Schmidt amplitudes, padded by zeros. Put
\[
J=D^{-2}\sum_{P}P^{\otimes4},\qquad H=M^{\otimes4},\qquad
A=(U_A^\dagger)^{\otimes4} J U_A^{\otimes4},\qquad
B=(U_B^{\mathsf T})^{\otimes4} J \overline{U_B}^{\otimes4}.
\]
The sum runs over sign-free Hermitian Paulis on one side. Each Pauli
expectation is real; its fourth power equals its fourth absolute
power. The coefficient-matrix expectation identity and
\(J^{\mathsf T}=J\) give the normalized stabilizer purity
\(D^2\operatorname{tr}(HAHB)\).
The Hilbert–Schmidt Cauchy–Schwarz inequality for
\(H^{1/2}AH^{1/2}\) and \(H^{1/2}BH^{1/2}\) bounds this by
\[
\sqrt{D^2\operatorname{tr}(HAHA)\;
      D^2\operatorname{tr}(HBHB)} .
\]
The two factors are the purities of paired frames. A bound on both
paired purities at a fixed spectrum therefore holds on the whole
two-unitary orbit. When the bound is the purity at the diagonal
matrix \(M\), the negative logarithm turns this attained purity
maximum into the entropy minimum.

For unequal qubit sides, pad the smaller side with leading local
\(\lvert0\rangle\) ancillas to make both dimensions \(D\).
This embeds each state under comparison and its sorted computational
representative in the corresponding balanced orbit. For each added
ancilla the normalized fourth Pauli moment factor is
\((1^4+0^4+0^4+1^4)/2=1\). The balanced comparison therefore
gives the desired inequality on the original cut.

## Exact assembly criterion

1. The [large fifth-to-seventh theorem](rank7_fifth_two_and_positive_shared_endpoints.md)
   covers \(0<\xi\le1/2\). The original exact upper run and
   [fourth-gap transfer](rank7_seed_branch_transfer.md) cover
   \(1/2\le\xi\le9/16\) with unrestricted \(a-b\).
2. The [lower-fifth proof](rank7_tied_fourth_lower_fifth.md) and its
   six completed traversals cover \(3/4\le\xi\le100/101\).
   For \(\xi\ge100/101\), ordering gives
   \(c/d\le b/d\le101/100\), so the
   [close-bottom theorem](rank7_near_two_tails.md) applies.
3. Every completed [upper bilinear traversal](rank7_fourth_tie_bilinear.md)
   proves the same comparison on its closed \(\xi\)-interval.
   The source and mathematical reduction were independently reviewed,
   including the [branches that transmit to arbitrary \(a-b\)](reviews/rank7_seed_branch_transfer_independent_review.md).
   Thus the remaining sufficient condition is a union of completed
   receipts covering \([9/16,3/4]\). In particular a common
   endpoint is included in each neighboring closed interval. Each interval
   proof uses the exact Pauli comparison in arbitrary qubit dimensions,
   so taking their union requires no dimension reduction.

Both choices of tail normalization follow from homogeneity of the
purity comparison, of degree four in the Schmidt probabilities.
The [excess-axis theorem](rank7_excess_ratio.md) covers either
nonpositive leading excess at every spectrum, and the paired
comparison already covers nonpositive exterior gain. The interval
certificates address the remaining frame sectors. This assembly
establishes existence of the sorted minimizer.

## Receipt check

Run the [exact interval union checker](../verification/verify_rank7_tail_interval_union.py)
with `--require-complete` at the end of the upper traversals. It checks
the frozen source hashes, requested rational endpoints, successful
completion markers, and equality of the counted leaf totals. It prints
the open gaps between completed closed intervals using exact fractions.
The C++ verifier supplies the certificate within each interval.

To reproduce an individual interval, compile
`verify_rank7_fourth_tie_bilinear.cpp` and use the two numerators
and the common denominator as arguments. The source includes the
directed-integer primitives from `verify_rank7_equal_fifth_sixth.cpp`.
For example, this invocation checks \([184/256,188/256]\).

```powershell
g++ -std=c++20 -O3 -Wall -Wextra -o cb_fourth_tie_bilinear.exe verification/verify_rank7_fourth_tie_bilinear.cpp
.\cb_fourth_tie_bilinear.exe 184 188 256
```

The first two cells in the current run are \([144/256,145/256]\)
and \([145/256,148/256]\). The following cells start at numerators
148, 152, 156, up to 188 and have width \(4/256\).
The [bilinear proof](rank7_fourth_tie_bilinear.md) links the logged
run for each completed cell.

## Independent review

Sol independently checked the endpoint union, the fourth-degree
homogeneity, closure of the frame sectors, the Pauli normalization
and transpose factors, and the leading-ancilla embedding. The receipt
parser's exact rational union and completion markers matched the C++
driver. On completion, the reviewer independently parsed all thirteen
receipts with exact fractions and ran the project's completion check.
Both checks gave the closed interval \([9/16,3/4]\) and
127,384,781 accepted leaves, comprising 66,051,783 older-region leaves,
2,293,425 weighted leaves and 59,039,573 bilinear leaves. The maximum
depth was 41 and the final cell had 8,554,105 accepted leaves.

The independent review covered the analytic reductions, the traversal
source and the completed local execution records. An independent
traversal replay can reproduce those records.

## Checkpoint

At 2026-11-18T09:41:06+00:00, the checker validated 13 completed receipts with 127,384,781 leaves. The target band is fully covered.
Both executable lanes completed. The MinGW g++ 16.2.0 executable built at 08:19 UTC has SHA-256 8e8a82917651a5c3ea22716b33a5c57b404e81f2d79a50c73186d26982ed17a2.
