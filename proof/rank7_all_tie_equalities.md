# Local Clifford equality at rank seven with repeated probabilities

November 18, 2026. Let \(\psi\) be a rank-seven bipartite pure
qubit state and \(\psi_{\rm CB}\) the sorted computational state
with the same Schmidt probabilities. Suppose at least one marginal
of \(\psi\) is diagonal in a stabilizer basis. Equality of their
order-two stabilizer Rényi entropies holds if and only if \(\psi\)
is a local Clifford image of \(\psi_{\rm CB}\), up to overall
phase. There is no restriction on multiplicities among the seven
positive probabilities.

Consequently at any spectrum with a strict paired margin against
the noncommuting Pauli defect, this classifies all unrestricted
physical equality states. This applies to the new
[three-equal-tail theorem](rank7_three_equal_tails.md) and the
[previous near-equal-four-tail theorem](rank7_near_equal_tails.md).

## Equality with one stabilizer marginal

Use local Cliffords so the marginal on \(A\) is diagonal in
computational labels. Write
\(\psi=\sum_{x\in S}\mu_x|x\rangle|u_x\rangle\), where all seven
\(\mu_x\) are positive and the \(u_x\) are orthonormal. This
choice works also inside degenerate Schmidt eigenspaces.
The one-stabilizer-basis comparison gives
\[
 F_2(\psi)\ \le\ T_2(\mu)\ \le\ F_2(\psi_{\rm CB}).
\]
Here \(F_2\) is the fourth Pauli purity and \(T_2(\mu)\) is
the aligned computational purity for the actual placement of
the weights on \(A\). This aligned purity can be evaluated in
two copies of the Hilbert space of \(A\), independently of the
dimension of \(B\). When equality holds, every positive-weight
term of the one-sided Pauli expansion has its normalized
coefficient equal to one. For the repeated tuple
\((x,x,x,x)\) in direction \(a=x+y\), its coefficient is
\(d_B^{-1}\sum_Q|\langle u_y|Q|u_x\rangle|^4\).
Parseval and unitary moduli at most one force every such modulus
to be zero or one. The terms with \(y=x\) identify \(u_x\) as
a stabilizer state, and the other terms force the \(u_y\) into
its Pauli orbit. Thus a Clifford on \(B\) makes
\(u_x=z_x|\pi(x)\rangle\) with a label injection \(\pi\).
[One-stabilizer-basis comparison and positive terms](one_stabilizer_marginal_optimality.md)

## The support and the spectral placement

For a computational placement, the normalized exterior overlap
is the sum of \(\prod_{x\in Q} t_x\) over affine four-point planes
\(Q\) in the support, where \(t_x=\mu_x^2\).
This plane polynomial is coefficientwise at most the sorted
reference in forward spectral gaps. Indeed, the ordered
zero-XOR quadruple sum is 24 times this plane polynomial plus
a symmetric repeated-index expression. Expanding each weight
into its nested top sets and applying the simultaneous binary
compression increases each coefficient of that quadruple sum.
The repeated-index expression, consisting only of terms with
all labels equal or two pairs equal, is unchanged.
[Coefficientwise binary compression](rank7_low_defect_interior.md)

In fact the aligned purity has the exact rank-seven formula
\[
 T_2(\mu)=\sum_x t_x^4+
       14\sum_{x<y}t_x^2t_y^2+
       168\sum_{Q\ {\rm affine\ plane}}\prod_{x\in Q}t_x .
\]
The zero displacement contributes repeated-label multiplicities
\(1,6\) and plane multiplicity 24. A nonzero displacement has at
most three parallel support edges. In the quotient by the
displacement, a zero-XOR tuple uses one edge four times or two
edges twice each. Every edge multiplicity must be even because
there are at most three distinct quotient labels. For a specified
edge pattern half of the 16 endpoint choices have zero XOR.
Thus a single edge contributes eight and a pair of edges
contributes \(6\cdot8=48\); the latter is counted in three
directions for each plane. This gives \(6+8=14\) and
\(24+3\cdot48=168\). Equality of \(T_2\) therefore forces equality
of the plane sum.
The coefficient of the fourth power of the smallest probability
is the number of planes. That gap is positive and there is no
cancellation between coefficient losses. Hence the support has
the reference count of seven planes.
[Aligned Pauli expression](one_stabilizer_marginal_optimality.md)

For seven binary labels let \(m_a\) count unordered pairs of
nonzero difference \(a\). Each \(m_a\le3\), total multiplicity
is 21, and three times the plane count is
\(\sum_a\binom{m_a}{2}\). The count of seven therefore forces
every nonzero multiplicity to be three. Translate so \(0\in S\).
Then \(S+S\) has eight points, and for every \(0\ne x\in S\),
\(S\cup(S+x)=S+S\) since the two sets meet at six points.
Thus \(S+S\) is invariant under translation by \(S\) and equals
its linear span. Undoing the translation, the support is an
affine three-space with one point removed. An affine Clifford
sends it to the seven standard labels
\(J=\{0,1,\ldots,6\}\subset\mathbb F_2^3\).

The following finite equality analysis handles every tie pattern.
Order the probabilities as \(t_0\ge\cdots\ge t_6>0\), with
forward gaps \(b_i=t_i-t_{i+1}\) for \(0\le i<6\) and
\(b_6=t_6>0\). A permutation places them at the labels in \(J\).
Its plane gain is a fourth-degree polynomial in the gaps, and
its nonnegative deficit coefficients depend only on which seven
four-wedges are planes for that permutation.

Enumerate the 5,040 placements and the 64 active subsets of
\(\{b_0,\ldots,b_5\}\). For any fixed placement equality holds
exactly when every positive deficit coefficient uses at least
one inactive gap. On the other hand two colorings of \(J\) by
equal-weight classes describe the same weighted spectrum up to
an affine Clifford precisely when they are in the same orbit
under the affine automorphisms fixing the missing label.
The [exact verifier](../verification/verify_rank7_all_tie_equalities.py)
checks equivalence of these two predicates. There are 30 plane
designs, 168 affine automorphisms, 6,300 forward coefficient
comparisons and 322,560 placement-and-tie cases. All 111,384
equality cases are affine colorings of the sorted reference.
The remaining code computes XOR plane incidences and integer
coefficient sums and compares finite sets. This puts the actual
spectral weights in sorted positions by a Clifford on \(A\),
even when repeated probabilities allow several placements.

## Alignment and phases with no simplicity assumption

For two parallel pairs \(x,x+a\) and \(y,y+a\) inside the support,
use the positive-weight tuple \((x,y,x,y)\) in the one-sided
expansion. The coefficient is zero if no Pauli on \(B\) can
connect both image pairs. Since the coefficient is one,
\(\pi(x)+\pi(x+a)=\pi(y)+\pi(y+a)\).
Hence the injection \(\pi\) carries all seven-point planes to
planes. In particular the planes through \(0,e_i,e_j\)
determine its values at \(e_i+e_j\). The three differences
\(\pi(e_i)+\pi(0)\) are linearly independent, because a
dependence would identify \(\pi(e_i+e_j)\) with some
\(\pi(e_k)\) or \(\pi(0)\). Thus \(\pi\) is an affine map on
this support. A Clifford on \(B\) now aligns the labels with
\(A\), including when the two ambient dimensions differ.

After alignment put \(w_a(x)=z_x\overline{z_{x+a}}\).
The same coefficient equality for paired tuples shows
\(w_a(0)^4=1\) by taking \((0,0,a,a)\) for each \(a\in J\).
Choose the overall phase so \(z_0=1\) and write
\(z_x=i^{f(x)}\). The tuple \((x,x,0,0)\) in direction \(a\)
gives \(w_a(x)^2=w_a(0)^2\) whenever \(a,x,x+a\in J\).
Thus \(f\) modulo two is linear, as seen on \(e_i,e_j\) and
\(e_i+e_j\). Local \(S\) gates remove this parity.
The remaining seven phases are signs. Every binary sign function
on \(0,e_i,e_i+e_j\) extends uniquely to a quadratic in the
three bits, with its coefficients determined in that order.
Local \(Z\) and \(CZ\) gates remove all these signs, completing
the local Clifford classification. The converse follows from
Clifford invariance.

## Transferring a strict paired margin

Suppose at a spectrum the paired comparison in every dimension
gives a strict margin proportional to the nonnegative
anticommuting defect \(J(C,C)\) whenever this defect is positive.
The paired Cauchy--Schwarz bound forces both paired sides to attain
the sorted value at an unrestricted physical equality state.
Consequently \(J(C,C)=0\) on both sides. The Pauli coefficients
of \(C\) with nonzero weight then commute pairwise by the
defining nonnegative anticommuting sum. Complete their group to
a maximal commuting Pauli group to obtain a stabilizer basis
diagonalizing the marginal. The earlier part now gives exactly
the local Clifford orbit. No distinctness of the probabilities
is used in any of these steps.
[Physical two-side equality transfer](rank7_unbounded_spread_equality_audit.md)
