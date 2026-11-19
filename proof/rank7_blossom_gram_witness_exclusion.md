# A Gram constraint from the blossom row excludes the six-mode witness

November 18, 2026. For every physical seven-frame, its 35 normalized
four-wedge weights have sup-norm distance greater than \(10^{-12}\)
from the rational table in the [six-mode slack note](rank7_six_mode_joint_slacks.md).
The exclusion holds in every local qubit dimension and yields a strict
linear inequality for convex mixtures of physical frames. It neither
closes the entire \(a=b\) family nor excludes every maximizer of the
packing relaxation. The quantitative bound is conservative.

Write \(V_I=q_F^{-1/2}\Pi_F x_I\), where \(q_F=4/D\), and
\(w_I=\|V_I\|^2\). For oriented lists the \(V_I\) are alternating.
The ambient wedge products between the \(V_I\) below are taken in
\(\Lambda^2 W_F\). They use the usual normalization
\(\|v\wedge u\|^2=\|v\|^2\|u\|^2-|\langle v,u\rangle|^2\).

## A physical inequality at every anchor

Fix a head \(i\) and write \(S_i\) for the six other labels in their
inherited orientation. For a partition of \(S_i\) into triples
\(T,T^c\), let \(\epsilon(T,T^c)\) be the sign of the resulting
concatenation. Set
\[
 {\cal P}_i=\sum_{\{T,T^c\}}
       \epsilon(T,T^c)\,V_{i,T}\wedge V_{i,T^c}.
\]
The ten summands are over unordered partitions. Both the sign and the
wedge change sign upon interchanging the two triples, so each term
is well defined. For \(j\ne i\) let
\(b_{ij}=\sum_{I\ni i,\ I\not\ni j}w_I\) be the six-mode blossom
row. Then
\[
             \boxed{\ \|{\cal P}_i\|^2\le b_{ij}(2-b_{ij}).\ }          \tag{1}
\]
This constraint applies to every choice of \(j\), using the same vector
on the left. In particular, a saturated blossom row forces
\({\cal P}_i=0\).

To prove (1) take \(x=x_i\), let \(\Omega\) be the unit five-volume of
the other labels except \(j\), and put
\(\Psi=\widetilde T_x^\dagger\Omega\). The six-mode blossom
identification gives \(\|\Psi\|^2=q_F b_{ij}\). The CAR and
compressed-swap identities in Sierant's Appendix C.6 read
\[
 2q_F I-\widetilde T_x^\dagger\widetilde T_x
      ={\cal H}_x^\dagger{\cal H}_x+q_F(I-\mathsf S_x),\qquad
 \mathsf S_x=({\cal V}_x^\dagger\otimes I)(I\otimes\Sigma)
                ({\cal V}_x\otimes I)
\]
with \({\cal V}_x\) isometric and \(\Sigma\) the literal exchange of two
\(W_F\) copies. Also \(\|\widetilde T_x\Psi\|^2\ge
|\langle\Omega,\widetilde T_x\Psi\rangle|^2=\|\Psi\|^4\).
Consequently
\[
 \|[I-(I\otimes\Sigma)]({\cal V}_x\otimes I)\Psi\|^2
               \le 2q_F b_{ij}(2-b_{ij}).
\]
In an adapted basis the component of \(\Psi\) on an oriented two-edge
\(K\subset S_i\setminus\{j\}\) is
\(\pm\sqrt{q_F}\,V_{i,S_i\setminus(\{j\}\cup K)}\).
The one-particle component of \({\cal V}_x x_K\) tested against
\(\overline{x_j}\) is \(q_F^{-1/2}\Pi_F(x_j\wedge x_i\wedge x_K)\).
The conjugation of the test vector follows by expanding in the real
computational basis and holds for arbitrary complex frames. Thus the
chosen component of the antisymmetrized double tensor is
\(\pm\sqrt{2q_F}\,{\cal P}_i\), since \(T=\{j\}\cup K\) selects
one representative of every triple partition. Taking its squared
norm proves (1).
[Propositions 4–5, equations (192), (195)–(198), and Lemma 14](https://arxiv.org/html/2609.13106v2)

## Exact obstruction at the rational table

Use
\[
 A=V_{0135},\ B=V_{0145},\ C=V_{0236},\ D'=V_{0246},\
 E=V_{1345},\ F=V_{0146},\ G=V_{2345}.
\]
Their squared norms at the table, in this order, are
\(1/2,1/4,1/2,1/4,1/4,1/4,3/4\).
The blossom rows \(b_{06},b_{36},b_{46}\) are saturated. The only
partition products with two nonzero factors in the three corresponding
sums give, with signs immaterial below,
\[
 A\wedge D'=\pm B\wedge C,\qquad C\wedge E=0,\qquad
 D'\wedge E=\pm F\wedge G.                                           \tag{2}
\]

For every unit \(y\) in the four-tail span, the existing physical
packing inequality \(w_{012y}\le1-\nu\) holds in the frame rotated to
include \(y\), with \(\nu=L_{01}+L_{02}-4\) unchanged. At this table
\(\nu=1/2\), and \(w_{0123}=w_{0124}=1/2\). The completion compression
on \(\operatorname{span}(x_3,x_4)\) is therefore precisely \(I/2\);
in particular \(V_{0123}\perp V_{0124}\).
[Rotated four-head bound](rank7_fourth_gap_lift.md)

Theorem 17 gives
\(\sum_z\langle V_{I,z},V_{J,z}\rangle=0\) for any distinct orthogonal
triple volumes \(I,J\), summing an entire ambient basis.
The triple rows \(013,014,023,024,015,026\) each have mass one in the
seven-frame, so all their outside completions vanish. Applying the
identity to the pairs \((013,014),(023,024),(015,026)\) gives
\[
             A\perp B,\qquad C\perp D',\qquad
                    |\langle A,C\rangle|=|\langle B,D'\rangle| .       \tag{3}
\]
In the first two identities the common completion from \(0123,0124\)
vanishes by the preceding orthogonality.
[One-hole unitary, Theorem 17](https://arxiv.org/html/2609.13106v2)

The first relation in (2) puts the four vectors in a common two-plane:
equal nonzero simple wedges have the same supporting plane, and if
both vanish then \(D'\parallel A\), \(C\parallel B\) directly.
In that plane \((A,B)\) and \((C,D')\) give two orthonormal bases
after normalization, so the two diagonal overlaps have equal modulus.
Their unnormalized scale factors, however, are \(1/2\) and \(1/4\).
By (3) both overlaps vanish. Thus \(C\parallel B\) and \(D'\parallel A\).
The second relation in (2) now puts \(B,C,E\) on one line \(\ell\).
Their squared norms sum to one.

The normalized rank-seven compression is a positive contraction
(Theorem 22), equivalently \(\sum_{I\subset[7]}|V_I\rangle\langle V_I|
\preceq I_{W_F}\), with the sum over four-wedges. Its expectation on
\(\ell\) implies every remaining \(V_I\perp\ell\).
The last identity in (2) is impossible: its left side is a nonzero
vector in \(\ell\wedge\ell^\perp\), and its right side belongs to
\(\Lambda^2\ell^\perp\).
[Rank-seven compression, Theorem 22](https://arxiv.org/html/2609.13106v2)

## Uniform separation and a linear cut

Assume that the 35 weights differ coordinatewise from the table by
at most \(\varepsilon=10^{-12}\), and let \(\delta=\sqrt{\varepsilon}\).
All \(V_I\) have norm at most one, and each formerly zero vector has
norm at most \(\delta\). Each blossom row contains ten terms, so (1)
gives \(\|{\cal P}_i\|\le5\delta\) for \(i=0,3,4\). The first and last
relations in (2) then hold with norm error at most \(13\delta\) after
discarding the other eight partitions. The middle relation has norm
error at most \(14\delta\). Here and below each sign is the exact sign
in the associated exterior identity.

The two leading pair totals have ten entries each, so
\(\nu\ge1/2-20\varepsilon\). The two-line completion compression
is bounded by \((1/2+20\varepsilon)I\) and its diagonal entries are
at least \(1/2-\varepsilon\). Positivity of the difference therefore
gives \(|\langle V_{0123},V_{0124}\rangle|\le21\varepsilon\).
Each formerly saturated triple has outside mass at most \(4\varepsilon\),
so the discarded outside inner product between two such rows has
modulus at most \(4\varepsilon\). The same three one-hole identities
used in (3) give
\[
 |\langle A,B\rangle|,\ |\langle C,D'\rangle|\le26\delta,\qquad
 \big||\langle A,C\rangle|-|\langle B,D'\rangle|\big|\le4\varepsilon.
\]
The first two comparisons each also discard one component with at least
one formerly zero factor. In the third, the completions 3 and 4 are
the only simultaneous nonzero slots inside the seven-frame.

Write hats for unit normalizations. The norms of \(A,C\) exceed
\(0.70\); those of \(B,D',E\) exceed \(0.49\). The normalized
\(A,B\) and \(C,D'\) inner products thus have modulus at most
\(76\delta\). The products \(\|A\|\|D'\|\) and \(\|B\|\|C\|\)
differ by at most \(5\varepsilon\), using
\(|\sqrt u-\sqrt v|=|u-v|/(\sqrt u+\sqrt v)\). Consequently the first
normalized wedge relation has error at most \(40\delta\).
Taking its inner product with \(\widehat A\wedge\widehat B\) gives
\[
 |s-t|\le192\delta,\qquad
 s=|\langle\widehat A,\widehat C\rangle|,\quad
 t=|\langle\widehat B,\widehat D'\rangle|.
\]
The previous unnormalized estimate yields
\((1/4-2\varepsilon)s\le4\varepsilon+(1/4+\varepsilon)192\delta\).
Hence \(s\le200\delta\) and \(t\le400\delta\).
Contracting the normalized wedge relation with \(\widehat B\) bounds
the distance of \(\widehat C\) to the line \(\ell=\mathbb C B\)
by \((40+76+400)\delta\). The middle relation in (2) bounds the sine
of the angle of \(E,C\) by \(42\delta\).
By the triangle inequality for line projectors, both \(\widehat C\)
and \(\widehat E\) have distance at most \(600\delta\) from \(\ell\).

The compression bound now leaves at most
\((3+360000)\varepsilon\) in total squared projections of the other
columns onto \(\ell\): the squared norms of \(B,C,E\) sum to at least
\(1-3\varepsilon\), and \(\|C\|^2+\|E\|^2\le1\).
Thus each of \(D',F,G\) has projection norm at most \(601\delta\).
Contract the last relation in (2) with \(\widehat B\). Its left norm
is at least \(0.49^2\sqrt{1-360000\varepsilon}-601\delta>0.23\);
the right norm is at most \(1202\delta\), and the norm error is at
most \(13\delta\). This contradiction proves the distance claim.

To obtain an affine inequality let \(Q(w)\) be the sum of the 22
weights at zero positions of the table and the 13 capacity slacks of
the following rows, in the complementary triple coordinates:

- Pair rows \(06,16,26,34,35,36,45,46\).
- Four-set rows \(1345,1356,2346\).
- Directed rows with ordered (present, absent) pairs \(30,40\).

All terms are nonnegative. On the 13 nonzero columns the matrix
\(M\) of these rows has determinant of magnitude four and
\(\|M^{-1}\|_\infty=25/4\). If \(w^*\) denotes the table, the
\(\ell^\infty\) norm of \(M(w-w^*)\) restricted to these 13 columns
is at most \(Q(w)\): each entry equals minus the corresponding row
slack minus the outside weight in that row. Each of the 22 remaining
weights is at most \(Q(w)\) as well. Therefore the strict affine
inequality
\[
                         Q(w)>(4/25)\,10^{-12}                          \tag{4}
\]
holds for every physical frame and every finite convex mixture of such
frames. The non-strict version holds on the closed convex hull.
[Exact table and matrix audit](../verification/verify_rank7_blossom_gram_witness.py)

## A separable completion price for the triangle probe

Let \(P=\max\{0,\nu,L_{01}-2\}\), \(x=1-\sum_{s=3}^6w_{012s}\),
and let \(R\) be the trace-one completion density of the leading
three-volume. For every rotated unit tail \(y\),
\(\langle y,Ry\rangle\le1-P\). If \(Q\) projects onto the four tails,
\(\|R^{1/2} Q R^{1/2}\|\le1-P\) and
\(\operatorname{Tr}(R^{1/2}(I-Q)R^{1/2})=x\). Thus
\(\lambda_{\max}(R)\le1-P+x\).
Set \(u=(P-x)_+\le1/2\). A probability vector with all entries at
most \(1-u\) has squared norm at most \((1-u)^2+u^2\), by transferring
mass to the largest entry until it reaches the cap.
The known completion purity inequality therefore gives
\[
              \eta\ge \frac{u(1-u)}{20}\ge\frac{u}{40}.                \tag{5}
\]
At the excluded table the necessary price would be \(\eta\ge1/80\).
Unlike the exclusion, (5) holds without any sparse-support hypothesis.
[Completion purity bound](rank7_six_mode_shared_probe.md)

## The full saturated face and its necessary Pauli price

The face \(d_s=D_6=D_{57}=x=0,\ \nu=1/2,\ d_1=1/4\) is larger than
the excluded point. Indeed each of its three nonnegative complementary
weights \(016,026,034\) in the table can be decreased independently
down to zero. Their actual wedges \(2345,1345,1256\) affect none of
these six equations, and decreasing a weight preserves all 119 upper
bounds. If the six-mode cardinality is also required to attain three,
decreasing \(034\) still preserves it. This gives exact alternative
points, without a numerical support search.

Nevertheless every physical frame on this entire face would satisfy
\[
             p_{01}p_{02}=p_{01}p_{12}=p_{02}p_{12}=0
                 \quad\text{at every odd Pauli label},                 \tag{6}
\]
and consequently \(\eta\ge\kappa\ge1/5\). Here
\(p_{ij}=|\langle x_i,Jx_j\rangle|^2\), \(p=p_{01}+p_{02}\),
\(r=p+p_{12}\). We give the argument because it uses information
about each Pauli label separately.

Let \(P=\operatorname{span}(x_0,x_1,x_2)\), \(M=\operatorname{span}(x_1,x_2)\),
\(Q=\operatorname{span}(x_3,x_4)\), \(V=\operatorname{span}(x_5,x_6)\),
\(Y=Q+V\), and \(S=P+Y\). By the exact \(D_{57}\) decomposition,
\(A_5=A_6=0\); since \(x=0\) the completion of the leading triple
is supported in \(Q\). Its two diagonal entries are both \(1/2\),
by the rotated bound above. The complement-pair row
\(A_3+A_4+T_{34}\le1\) gives \(T_{34}=0\), so all three wedges with
two leading legs and the plane \(Q\) have zero weight.

Sum the four directed rows for wedges containing 0 and missing one
specified tail. A wedge containing all three heads occurs three times,
one with \(0\) and exactly one other head occurs twice, and a wedge
with \(0\) and three tails occurs once. The first two contributions
already total \(3+2(9/2-2)=8\). Therefore every \(0\)-plus-three-tail
wedge has zero weight and every such directed row is saturated. The
total occupancy of \(0\) is \(7/2\), so \(L_{0i}=3/2\) on every tail.
For \(i=3,4\), the completion row totals for \(01i,02i\) sum to
\(L_{0i}+A_i=2\), and each is at most one. All four triples thus
have their complete one-hole mass inside \(S\). The triples \(015,026\)
do also: their complement four-set rows \(2346,1345\) occur with
positive price in the saturated certificate for \(d_1=\nu/2\).
[Eight-row comparison and \(D_{57}\)](rank7_six_mode_joint_slacks.md)

Fix an odd skew Pauli antiunitary \(J\) with \(p>0\). The compression
to \(P\) has a unit kernel vector \(n\) and sends it to the unit
outside completion \(t=Jn\in Q\). This holds label by label because
the leading completion density is an average of nonnegative line
projectors with strictly positive weight at this label. Choose a
unit \(\ell\in Q\ominus\mathbb Ct\). Every four-wedge of zero weight
has zero four-by-four Pfaffian at each skew Pauli, by the squared
Pfaffian formula. In particular the Pfaffians on \((n,u,t,\ell)\)
vanish for \(u\in P\ominus\mathbb Cn\) by \(T_{34}=0\).
Since \(n,t\) are paired exactly by \(J\), these equalities imply
\(J\ell\perp P+Q\).
[Pauli Pfaffians and kernel completion](rank7_triangle_quantitative_rigidity.md)

The triples \(01\ell,02\ell\) have no outside-\(S\) Pfaffian, by
linearity and the four saturated rows. Of their two corresponding
leading-edge amplitudes at least one is nonzero. As \(J\ell\perp P\),
the outside Pfaffian equation for that edge reduces to its nonzero
amplitude times the outside component of \(J\ell\). Thus
\(v'=J\ell\) lies in \(V\). The Pfaffian at
\((x_0,t,\ell,v')\) vanishes by the zero \(0\)-plus-three-tail
occupancy. Contracting the exactly paired \(\ell,v'\) leaves
\(\langle x_0,Jt\rangle=0\). Since \(Jt=-n\), it follows that
\(n\in M\), so \(p_{12}=0\).

Let \(z\) span \(M\ominus\mathbb Cn\) and let \(v''\) span
\(V\ominus\mathbb Cv'\). The four-space
\(\operatorname{span}(n,t,\ell,v')\) is invariant under \(J\).
Its orthogonal complement inside \(S\) is
\(G=\operatorname{span}(x_0,z,v'')\). The Pauli compression on \(G\)
has a nonzero leading pair \(x_0,z\); therefore its kernel is sent
by \(J\) to a unit vector outside \(G\). This image is also orthogonal
to the invariant four-space, so the full \(G\)-volume has nonzero
completion outside \(S\).

Expand triple \(015\) using \(x_1\in\operatorname{span}(n,z)\) and
\(x_5\in\operatorname{span}(v',v'')\). Only its component on
\(\Lambda^3G\) can have an outside Pfaffian. Components with just one
of \(n,v'\) have this leg in an invariant pair, orthogonal under
the skew form to their other two \(G\) legs and to every outside
leg. The component with both \(n,v'\) uses different invariant pairs
and likewise vanishes. The same expansion holds for \(026\).
Their saturated completion rows thus give
\[
 |\langle z,x_1\rangle\langle v'',x_5\rangle|
   =|\langle z,x_2\rangle\langle v'',x_6\rangle|=0 .
\]
If both \(x_1,x_2\) overlaps were nonzero, \(v''\) would be orthogonal
to \(V\). Hence \(z\) equals one of these two lines, and at most one
of \(p_{01},p_{02}\) is nonzero. When \(p=0\) this part is automatic.
This proves (6).

It follows that \(\kappa=\kappa_{01}+\kappa_{02}\),
\(\eta=\kappa+\kappa_{12}\), where \(\kappa_{ij}=\langle p_{ij}(1-p_{ij})\rangle\).
The individual physical inequality \(L_{ij}-2\le(5/2)\kappa_{ij}\)
now implies \(\nu\le(5/2)\kappa\). This proves the necessary
\(1/5\) price across the face. It does not establish that the whole
face is physically empty.
[Individual Pauli price](rank7_highest_pair_geometry_five_halves.md)
