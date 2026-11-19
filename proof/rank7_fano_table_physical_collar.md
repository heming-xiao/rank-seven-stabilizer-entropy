# An exterior-weight neighborhood of the sorted computational table

Let \(t_0\ge\cdots\ge t_6>0\) be the paired probabilities, and put
\(s=t_6/t_0\). For the standard seven Fano four-sets
\(\mathcal F=\{0123,0145,0246,0356,1256,1346,2345\}\), set
\[
 \epsilon_*(s)=\min\{(4\cdot10^9)^{-1},\,s^3/(14\cdot10^6)\}.
\]
If every \(w_I\ge1-\epsilon_*(s)\) for \(I\in\mathcal F\), the
paired frame's stabilizer purity is at most the sorted computational
value on every local qubit dimension. Consequently a violating paired
frame must satisfy the **affine** inequality
\[
                    7-\sum_{I\in\mathcal F}w_I>\epsilon_*(s).        \tag{1}
\]
This is a necessary condition on a putative violation, so a search
for a violating physical frame can impose it. It rules out
arbitrarily small displacements toward the computational weights
within the closed convex hull of violating frames (with a
nonstrict inequality on that closure).

## One nearly saturated four-wedge

Fix \(I\) with \(w_I\ge1-\epsilon\) where \(\epsilon\le\epsilon_*(s)\).
For a fixed odd skew Pauli label, its skew form on the four-plane
has two singular pairs with squared singular values \(u\ge v\).
The squared Pfaffian is \(uv\), and the sum of six squared pair
entries is \(u+v\). On any hyperplane in this four-space the sum
\(r\) of its three squared entries satisfies \(v\le r\le u\):
in a basis ending in the unit normal, the part omitted from
\(u+v\) is the squared norm of the skew matrix acting on the
conjugate of that normal, between \(v\) and \(u\).
Since \(0\le v\le u\le1\),
\[
  r(1-r)\le u(1-v)\le u+v-2uv .
\]
The normalized odd-Pauli average gives \(\langle u+v\rangle=6\)
by pair completeness and \(\langle uv\rangle=3w_I\) by the Pfaffian
identity. Hence every three-face of \(I\) has triangle defect at
most \(6(1-w_I)\le 6\epsilon\). The threshold
\(6/(4\cdot10^9)<(50176\cdot12000)^{-1}\) permits the
[triangle rounding theorem](rank7_triangle_quantitative_rigidity.md).
For three chosen basis vectors of \(I\) it gives a rank-four
stabilizer code \(Q_I\) such that their summed squared leakage
\(a\le2\eta\le12\epsilon\). Zero defect follows from the corresponding
[exact theorem](rank7_triangle_zero_and_joint_geometry.md).

Write \(e\) for the fourth basis vector's squared leakage from
\(Q_I\). After Clifford conjugation \(Q_I\) is an affine four-point
coordinate block. Any four-wedge with precisely one leg orthogonal
to that block and three legs within it has zero projection to \(F\),
by the affine XOR rule. Expand the first three vectors into their
code projections and outside components, leaving the fourth vector
intact. The all-code triple contributes normalized wedge norm at
most \(\sqrt{1-e}\). The three terms with exactly one of the
first three outside contribute together at most \(\sqrt{3ae}\).
The terms with at least two of the first three outside sum to at
most \(a+(a/3)^{3/2}\le4a/3\), by the normalized decomposable
wedge norm bound and \(a\le3\). Therefore
\[
    1-\epsilon\le\sqrt{w_I}\le
       \sqrt{1-e}+\sqrt{3ae}+4a/3
       \le1-e/4+13a/3 .
\]
It follows that \(e\le4\epsilon+(52/3)a\le212\epsilon\).
Thus each of the four basis vectors indexed by \(I\) has squared
leakage at most \(\delta=212\epsilon\) from \(Q_I\).

## Assembling all seven codes

Distinct reference four-sets share two labels. Choose one common
vector \(x_i\) for any two codes. After setting the generator signs
to define their positive character, every Hermitian Pauli generator
in either stabilizer has expectation at least \(1-2\delta\) on
\(x_i\). Two anticommuting Hermitian Pauli operators have squared
expectations summing to at most one; \(2(1-2\delta)^2>1\) excludes
anticommutation. Thus the generators of all seven codes commute.
Extend their binary isotropic span to a maximal isotropic space
and use the associated simultaneous stabilizer basis. In that basis
each \(Q_I\) is the coordinate projector of a four-point affine plane
\(B_I\). Consistency of signs is required only within each individual
code. Distinct character blocks across codes are allowed.

For \(i\in I\), \(x_i\) has probability at least \(1-\delta\) in
\(B_I\). For \(i\notin I\), that probability is at most \(4\delta\),
since the four orthonormal \(x_j,\ j\in I\), already account for
at least \(4-4\delta\) of the trace of \(Q_I\). Let \(D_i\) be the
coordinate cell with the exact membership pattern of \(i\): inside
every \(B_I\) with \(i\in I\) and outside every other \(B_I\).
A given label belongs to four of the seven reference four-sets.
The union bound therefore gives \(x_i\)-mass at least
\(1-4\delta-3(4\delta)=1-16\delta>0\) in \(D_i\).
The seven patterns are distinct, so these cells are disjoint.
For each \(I\), \(B_I\) contains the four nonempty cells \(D_i\),
\(i\in I\). It has exactly four coordinate points; hence these
cells are singletons and fill \(B_I\).

The seven resulting points contain all seven distinct affine
four-planes \(B_I\). They lie in one affine eight-point space:
for each nonzero realized difference \(a\), the number \(m_a\)
of pairs with that difference is at most three, with
\(\sum m_a=21\). Seven planes require
\(\sum_a\binom{m_a}{2}=21\), forcing every \(m_a=3\).
Consequently the difference set has eight elements. Translating
the seven points to contain zero, the difference set equals the
union of the original set and each of its nontrivial translates by
a point of the set, because their intersection has six points.
Translation by each such point preserves the union, so it is their
eight-point linear span.

Let \(H\) be this eight-point stabilizer code. Normalize \(t_0=1\).
The total weighted leakage of the paired probability matrix from
\(H\) is at most \(7\cdot16\delta=112\cdot212\epsilon\le s^3/560\).
The [direct near-eight-space comparison](rank7_low_defect_interior.md)
then proves the desired exterior and paired-purity bounds.
Taking the contrapositive and using \(w_I\le1\) gives (1).
The code assembly and numerical thresholds have a
[standard-library verifier](../verification/verify_rank7_saturated_face_separation.py).

## A total-deficit bound for every permuted Fano table

Let \(\mathcal F'\) be the image of the seven reference four-sets
under any permutation of the frame labels, and set
\(B_{\mathcal F'}=\sum_{I\in\mathcal F'}(1-w_I)\).
The code construction above gives the stronger condition
\[
 c_{\rm F}(C)>c_{\rm F}(C_{\rm CB}) \quad\Longrightarrow\quad
 B_{\mathcal F'}>
 \min\{(4\cdot10^9)^{-1},\,s^3/250880\},
 \qquad s=t_6/t_0 .                                                   \tag{2}
\]
This applies also to a paired purity violation. The lower bound
may be taken weakly on the closed convex hull of the physical
positive-exterior-gain frames for the fixed spectrum.

To prove (2), write \(\epsilon_I=1-w_I\ge0\) and assume
\(B_{\mathcal F'}\) is at most the right side of (2). Apply the
one-face argument with \(\epsilon_I\) for each plane. Its four
incident vectors have total squared leakage
\(\ell_I=a_I+e_I\le224\epsilon_I\). For the other three vectors,
orthogonality and rank four give
\[
      \sum_{i\notin I}\|Q_Ix_i\|^2
       \le 4-\sum_{i\in I}\|Q_Ix_i\|^2=\ell_I .
\]
The commuting-code and membership construction is unchanged.
Summing the union bound over all seven membership cells now
gives total squared leakage at most \(2\sum_I\ell_I\le448 B_{\mathcal F'}\).
Every cell is nonempty since that sum is less than one.
All seven singleton cells lie in a common affine eight-space
by the earlier incidence proof. Normalizing \(t_0=1\), the
weighted leakage is at most \(448 B_{\mathcal F'}\le s^3/560\),
which gives the exterior bound. The construction only uses
the incidence properties of the chosen Fano table, and the
low-leakage theorem compares the actual spectrum to its
sorted computational value for every orientation of that
spectrum inside the affine eight-space. This proves (2) for
all 30 distinct permuted designs.

In the currently remaining spectral domain \(s>1/231\), the
weak rational row \(B_{\mathcal F'}\ge1/(250880\cdot231^3)\)
can be imposed for every design when testing for a positive
physical exterior gain. [Incidence and constant checks](../verification/verify_rank7_physical_cut_interface.py).


## Three nearly saturated Fano planes suffice

The argument for (2) needs only three faces with the incidence
pattern of \(0123,0145,0246\). The membership patterns of the seven
labels in these three faces are the seven nonzero three-bit strings.
The three rounded codes commute by their shared frame vectors. The
same trace bound gives total cell leakage at most \(448 B\), where
\(B\) now sums the deficits of only these three four-wedges. The
membership cells are all nonempty and singleton because each code
contains four of them. In the common binary coordinates the three
planes determine points 3, 5 and 6 from the four points 0, 1, 2 and
4 by XOR. Their affine span is three-dimensional since it contains
seven distinct points. The low-leakage theorem therefore applies
with the same threshold.

The construction works after any permutation of labels. In any
Fano table, a triple of planes sharing exactly one label has this
incidence pattern. There are 28 such triples within each of the 30
tables and 840 distinct triples across them. Each positive physical
exterior gain must satisfy
\[
 3-\sum_{I\in\mathcal T}w_I>
 \min\{(4\cdot10^9)^{-1},(d/\alpha)^3/250880\}
\]
for every such triple \(\mathcal T\). The weak inequalities extend
to the closed convex hull of the positive-gain physical frames.
[Exact incidence checks](../verification/verify_rank7_physical_cut_interface.py).
