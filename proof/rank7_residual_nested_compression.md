# Exterior compression alone settles the strictly ordered residual spectrum

November 18, 2026. Let the positive Schmidt probabilities be proportional to
\[
 (79/10,19/5,17/10,7/5,13/10,11/10,1).
\]
For every complex seven-mode frame, write \(E\) for the normalized linear
exterior-overlap gain above the sorted computational reference and
\(\mathcal D_F\) for the normalized actual four-wedge compression loss.
Then
\[
  E\ge0 \quad\Longrightarrow\quad \mathcal D_F\ge(44/25)E .
  \tag{1}
\]
The signed term in the single-frame purity comparison is
\(168E-96\mathcal D_F\), so (1) proves global optimality of the sorted
representative for all qubit bipartitions. It retains at least
\(1/176\) of the compression loss on positive-gain frames and leaves the
separate Pauli defects fully available. Frames with \(E\le0\) retain all
of those losses. Homogeneity gives the statement for normalized probabilities;
the standard strict-margin transfer gives a full relative open neighborhood of
seven-mode spectra. [Compression identity and single-frame comparison](rank7_compression_slack_astra.md) · [Two-frame transfer and neighborhoods](rank7_open_interior_neighborhood.md)

## A test at any fixed spectrum

Let \(t_I=\prod_{i\in I}t_i\) and sort the 35 numbers \(\sqrt{t_I}\)
in increasing order \(a_0,\ldots,a_{34}\). Take \(a_{-1}=0\).
With \(R_j\) the coordinate projector onto wedges at or above the \(j\)-th
amplitude, let \(s_j=\operatorname{Tr}(R_jT)\), where
\(0\preceq T\preceq I\) is the actual normalized four-wedge compression.
Thus \(s_j\) is a linear function of the physical occupancies
\(w_I=T_{II}\). Equal amplitudes can be grouped. With
\(\phi(z)=(z-\lfloor z\rfloor)(1-z+\lfloor z\rfloor)\),
the nested spectral inequality gives
\[
 \mathcal D_F\ge\sum_j(a_j-a_{j-1})^2\phi(s_j).
 \tag{2}
\]
In detail, the non-projection part of \(\mathcal D_F\) weights
\((T-T^2)_{II}\) by \(t_I\). The other part weights \(|T_{IJ}|^2\) by
\((\sqrt{t_I}-\sqrt{t_J})^2\) for \(I<J\). A squared sum of nonnegative
gaps dominates their summed squares. Consequently these parts dominate
the sum of squared gaps times
\(\operatorname{Tr}[(R_jTR_j)(I_{R_j}-R_jTR_j)]\), taken on
\(\operatorname{ran}R_j\).
Minimizing that last trace over contractions with trace \(s_j\) gives
\(\phi(s_j)\) by filling the eigenvalues up to one successively.
[Nested spectral rounding](rank7_compression_slack_astra.md)

On any polyhedral cell of a physical packing relaxation, certify
\(l_j\le s_j\le h_j\) by linear duals. Form the linear interpolation of
\(\phi\) through \(l_j,h_j\) and all integers in that interval. This is convex
and lies below \(\phi\). Indeed on each unit interval the interpolation is
a chord of a concave quadratic. With an integer inside the cell, the segment
slopes are nonpositive, then zero if consecutive integers occur, then
nonnegative. The maximum of the affine segment extensions is thus a
valid lower bound on \(\phi\). A single variable \(z_j\ge0\) constrained
by these affine lines represents the interpolant in a minimization.
The resulting bound is an ordinary LP with exact rational coefficients
when the spectral squares and lower bounds for the squared gaps are rational.
This construction can be reused at any spectrum; its sufficiency depends
on the resulting linear programs.

## Three rational cells

Restrict to \(E\ge0\) and impose the 98 unconditional physical packing
rows and the 21 upper bounds \(L_{ij}\le7/3\). The first split is at
\(s_0=\operatorname{Tr}T=19/3\). For \(s_0\ge19/3\) the second split
is at \(s_{17}=7/2\), with the corresponding threshold beginning at
wedge \(0346\). The retained sorted indices are
\[
 0,5,7,14,17,20,23,24,25,26,27,29,30,31,33,34 .
\]
All nineteen omitted indices have nonnegative contributions in (2). Thus (2)
may always be evaluated on any subset of indices using their original
adjacent gaps.

For each cell the program upper-bounds
\((44/25)E-\sum_j m_j z_j\), where \(m_j\) is a rational lower bound on
the squared adjacent gap, obtained by integer square roots and downward
rounding. The three certified upper bounds, expressed as lower margins
for (1), are respectively greater than \(17/1000\), greater than
\(14/1000\), and exactly zero. The zero-margin cell includes the
computational equality case. Together they cover all physical frames.
[Original packing rows](rank7_forward_coefficients_independent.md) · [Universal pair cap](reviews/rank7_two_link_independent_review.md)

The [standard-library verifier](../verification/verify_rank7_residual_nested_compression.py)
uses the [stored prices](../certificates/rank7/rank7_residual_nested_compression.json) to check
96 lower and upper trace endpoints and the three terminal duals. During a
range check it explicitly charges any uncovered column coefficient at
\(w_I\le1\); complementary pairs already imply these bounds. The terminal
duals have exact column coverage without corrections, including their
auxiliary \(z_j\) columns. Run
\(\texttt{python verify_rank7_residual_nested_compression.py}\).
The optional \(\texttt{--generate}\) mode rediscovers the prices using
SciPy and rational basis reconstruction in SymPy, then verifies them
before saving.

For the previous [exact relaxation array](../verification/verify_rank7_split_relaxation_witness.py)
the sixteen rounded contributions by themselves sum to \(55243/72000\).
The required \((7/4)E\) is \(86611/120000\), which is smaller by
\(8191/180000\). Thus any contraction with these diagonal occupancies
already incurs sufficient compression loss. The test does not need a
judgment on whether that particular array can be realized by a physical
frame. The proof above treats all possible physical occupancies.

