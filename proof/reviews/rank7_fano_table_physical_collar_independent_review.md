# Independent review of the computational Fano-table neighborhood

November 18, 2026.

The proposed all-dimension implication holds with
\(\epsilon_*(s)=\min\{1/(4\cdot10^9),s^3/(14\cdot10^6)\}\)
for \(s=t_6/t_0\). If all seven reference occupancies are
at least \(1-\epsilon_*(s)\), the normalized exterior gain
is nonpositive on that physical frame.
[Main proof](../rank7_fano_table_physical_collar.md).

For each high reference four-wedge, the squared singular
pairs of the restricted skew Pauli are \(u\ge v\).
Removing one leg subtracts a squared norm between these
values from the six-entry sum \(u+v\). Thus the triangle
mass is in \([v,u]\), and its defect integrates to at most
\(\langle u+v-2uv\rangle=6(1-w_I)\). The small-defect rounding
threshold is met because \(6\cdot50176\cdot12000<4\cdot10^9\).
The three chosen legs have summed leakage at most
\(12\epsilon_*(s)\). In a Clifford coordinate system for
the resulting four-point code, any projected four-wedge
with exactly one outside leg vanishes by XOR.
If the three-leg leakage is \(a\) and the fourth leakage
is \(e\), the remaining expansion gives
\[
 1-\epsilon\le\sqrt{1-e}+\sqrt{3ae}+4a/3
             \le1-e/4+13a/3 .
\]
The last bound uses \(\sqrt{3ae}\le e/4+3a\).
Consequently \(e\le4\epsilon+(52/3)a\le212\epsilon\).

Independently enumerating the seven Fano sets confirms that any
two have two common labels, each label belongs to four sets,
and all seven incidence signatures are distinct. Each code's
Hermitian Pauli generators have absolute expectation at least
\(1-424\epsilon\) on a common incident vector. Since
\(2(1-424\epsilon)^2>1\), a generator of one code cannot
anticommute with a generator of any other. A simultaneous
Clifford coordinate basis therefore turns every code into a
four-point affine plane. Different codes may use different
characters of the common commuting group.

In that basis each incident membership condition loses at most
\(212\epsilon\) squared mass. A nonincident condition loses at
most \(4\cdot212\epsilon\) by the rank-four trace bound on
the four orthonormal incident vectors. Thus each vector has
squared mass at least \(1-16\cdot212\epsilon>0\) in its exact
membership cell. The cells are disjoint. Each code contains
the four distinct nonempty cells of its incident labels.
Its rank four makes each such cell a singleton and these cells
fill the code. The resulting seven distinct coordinates lie
in one affine three-space. In fact the plane identities for
\(0123,0145,0246\) express coordinates \(3,5,6\) as the
respective sums of coordinates \((0,1,2),(0,1,4),(0,2,4)\).
Their affine span therefore has dimension at most three,
and seven distinct points require dimension at least three.

After normalizing \(t_0=1\), the weighted leakage from
the common affine eight-point code is at most
\(7\cdot16\cdot212\epsilon=23744\epsilon\).
The rational check \(560\cdot23744<14\cdot10^6\) puts it below
\(s^3/560\). The existing low-support comparison applies in
the common Clifford basis and yields nonpositive exterior
gain using only the weighted leakage. Every positive
exterior-gain frame has
\(7-\sum_{I\in\mathcal F}w_I>\epsilon_*(s)\).
The weak affine inequality transfers to the closed convex hull
of those positive-gain frames at fixed \(s\). Its application
to a proposed table on a ray from the computational reference
requires that the table is to be realized as a single physical
frame with positive exterior gain.
[Existing low-support comparison](../rank7_low_defect_interior.md).

## Total deficits and the three-plane refinement

For each selected plane \(I\), use its own error
\(\epsilon_I=1-w_I\). The total incident leakage from its
rank-four code is \(\ell_I=a_I+e_I\le224\epsilon_I\).
By orthogonality and the rank-four trace, the total probability
of the other three legs in this code is at most \(\ell_I\).
Summing the membership-cell union bound over all seven legs
therefore loses at most \(2\sum_I\ell_I\le448B\), where \(B\)
is the sum of the selected plane deficits. This bounds each
individual leakage as well, so \(448B<1\) makes every required
cell nonempty. The normalized spectral leakage is at most
\(448B\), and \(448\cdot560=250880\) gives the stated threshold.
For the weaker remaining-domain row,
\(250880\cdot231^3>4\cdot10^9\) verifies the use of the same
constant when the minimum also contains \(1/(4\cdot10^9)\).

When the absent eighth point is translated to zero, the seven
planes are the level-one sets of the seven nonzero binary
linear functionals. Three such planes share one point precisely
when the three functionals are independent, and their seven
membership signatures are then all nonzero three-bit strings.
There are \(7\cdot6\cdot4/6=28\) choices per table.
Across permutations, assigning the seven signatures to the
seven labels gives \(7!\) ordered assignments. Permuting the
three plane positions is the only repetition for unordered
sets, giving \(7!/3!=840\). Each rank-four plane again fills
its four nonempty cells, and the three plane XOR equations
give a common affine eight-point code. The same total leakage
estimate applies to the three selected planes. Each weak
seven-plane inequality is implied by the three-plane
inequalities because all individual deficits are nonnegative.

At fixed spectrum the strict necessary inequalities apply to
physical frames of positive exterior gain. Their weak versions
hold on the closed convex hull of that subset, by affinity.
The exterior-collar proof excludes a near-reference table
proposed as a single positive-gain frame. A formal mixture
of the reference with a gain-positive relaxed point can still
have positive exterior gain.

## Exact remaining packing witness

I independently rebuilt the 119 rows and the 840 three-plane
patterns for the existing relaxed witness \(w^*\) at
\(t=(79/10,19/5,17/10,7/5,13/10,11/10,1)\).
Its minimum three-plane deficit is \(7/6\), attained at the
reference triple \(\{0123,2345,1256\}\). The minimum among the
30 seven-plane deficits is 4. Thus on the full affine segment
\(w_\lambda=(1-\lambda)w_{\rm CB}+\lambda w^*\), the minimum
three-plane deficit is exactly \(7\lambda/6\): all reference
deficits are nonnegative and the displayed triple has reference
deficit zero.

The exact collar threshold for this spectrum is \(1/(4\cdot10^9)\).
The three-plane rows therefore trim the relaxed ray only up to
\(\lambda=3/(14\cdot10^9)\), with the endpoint retained by the
weak version. At \(\lambda=1/2\), all 119 packing rows and all
840 collar comparisons still pass. The normalized exterior gain
is \(12373/60000\) and the minimum three-plane deficit is \(7/12\).
This is an exact obstruction to proving nonpositive exterior
gain using these packing rows and the collar alone. It supplies
neither a physical realization nor a gain of actual paired
purity, which also depends on the physical defects.
[Relaxed witness](../../verification/verify_rank7_split_relaxation_witness.py) ·
[Incidence checks](../../verification/verify_rank7_physical_cut_interface.py).
