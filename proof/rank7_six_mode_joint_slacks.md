# Two tail prices and their exact exterior slacks

November 18, 2026. For any ordered positive spectrum
\((\alpha,\beta,\gamma,a,b,c,d)\), the conditional leading-edge matching
admits two distinct prices with all three computational leading directions
saturated. The associated sixth-mode highest-pair deficit pays
\(\max\{v,\nu/2,0\}\). In particular a single computable linear statistic
controls both positive excesses, even when the fourth and fifth
probabilities coincide. Sections below give the simultaneous physical
payments and the exact limitation of these exterior slacks.
[Physical probe notation](rank7_six_mode_shared_probe.md)

Set \(H=b(c-d)\), \(R=d(b-c)\), and distinguish the symbol \(r\) for
the leading triangle's skew weight. In a seven-vertex matching let
\(k_6\) count edges entirely inside vertices \(0,\ldots,5\), and
let \(k_5\) count the used vertices among \(0,\ldots,4\).
Each matching satisfies
\[
 \mathrm{score}\le M_{\rm type}-H(3-k_6)-R(5-k_5).                  \tag{1}
\]
Here the four maxima \(M_{\rm type}\) are the original conditional maxima
for leading edges \(01,02,12\) or for no leading edge. Their successive
differences are \(\Delta,g,j\).
[Conditional maxima](rank7_general_two_probe_matching.md)

For a full matching, omitting label 6 requires no decrement. Omitting
label 5 costs at least \(H\): in a leading type the completion loses
\(b(c-d)\), and in the empty type \(\gamma(c-d)\). Omitting any vertex
among \(0,\ldots,4\) costs at least \(H+R=c(b-d)\). For a fixed leading
edge the remaining weights are \(z,a,b,c,d\), with \(z\ge a\), and the
two completion edges then score at most \(za+cd\). In the empty type,
omitting a top-five tail gives score at most
\(\alpha a+\beta c+\gamma d\); omitting a head gives at most
\(\alpha a+\beta b+cd\). Compare both with \(\alpha a+\beta b+\gamma c\).
The sorted computational matchings of the three leading types respectively
omit 6, 5, and 4, attaining precisely the charged maxima.

For partial matchings, reduce each edge score by \(H\) if both endpoints
are below 6, and by \(R\) per endpoint below 5. Every adjusted edge is
nonnegative. The least edge inside the first five is bounded below by
\(b^2-H-2R=(b-c)(b-d)+cd\), while an edge joining those five to 5 or
6 has score at least \(cd\). Thus one can complete any leading type.
In the empty type, two disjoint tail-tail edges could block extension.
Replace one endpoint of a tail-tail edge by an unused head and then
extend. This replacement cannot lower the adjusted score. For an endpoint
among 3 and 4 the tax is unchanged, for endpoint 5 the gain before
tax is at least \((b-c)d=R\), and for endpoint 6 it is at least
\((b-d)c=H+R\). The same argument permits completing any shorter
empty-type matching.

## Signed physical polarization

Let \(z_6=L_-(P_6)\) as before. Write
\[
 z_{57}=\mathcal A(P_5\otimes P_7+P_7\otimes P_5)|_{\Lambda^2}.
\]
This equals the mixed projection of the edge-weight operator with
diagonal entries \(1_{i<5}+1_{j<5}\) on each of the 21 two-wedges.
For each odd Pauli write \(s_6\) and \(k_5\) for its matching expectations
of the two statistics. With \(p=p_{01}+p_{02}\) and \(r=p+p_{12}\),
the computational moments in the three directions are
\[
  \langle p_{01}s_6\rangle_*=3,\quad
  \langle p s_6\rangle_*=5,\quad
  \langle r s_6\rangle_*=7,\quad \langle r k_5\rangle_*=14 .
\]
Set \(d_s=3-W_6\) for the previous shared six-mode statistic and put
\[
 d_1=2-\sum_{I\ni0,1,\ 6\notin I}w_I,\qquad
 D_6=4-W^\triangle_6,\qquad D_{57}=8-W^\triangle_{57}.
\]
Here \(W^\triangle_6\) counts, with multiplicity, four-wedges avoiding
6 and containing a leading edge. \(W^\triangle_{57}\) sums for each
leading edge in a wedge the number of its two other vertices below 5.
For \(x=1-\sum_{i=3}^6 A_i,\ A_i=w_{012i}\), let
\(K_{ij}=1-A_i-A_j-T_{ij}\ge0\), with \(T_{ij}\) the total of the
three four-wedges consisting of a leading edge and the tail pair \(ij\).
The triangle margins are exactly
\[
 D_6=x+A_6+\sum_{3\le i<j\le5}K_{ij},\qquad
 D_{57}=2x+A_5+A_6+
     \sum_{3\le i<j\le6}(1_{i\le4}+1_{j\le4})K_{ij}.                \tag{2}
\]
Indeed \(W^\triangle_6=3\sum_{i\le5}A_i+\sum_{i<j\le5}T_{ij}\).
Writing \(u_i=1_{i\le4}\) for tails, the other total is
\(3\sum_i(1+u_i)A_i+\sum_{i<j}(u_i+u_j)T_{ij}\). Substituting the
definition of \(K_{ij}\) proves both identities.

Apply (1) to each Pauli matching distribution, multiply by the indicated
leading probe weight, and use the mixed-sector polarization identity.
The earlier shared and highest inequalities now have the respective
additional terms
\[
\begin{array}{ll}
 H[d_s+2\langle u,z_6\rangle]+R\langle p(5-k_5)\rangle,
 &\text{shared},\\
 H[d_1+2\langle u_1,z_6\rangle]+R\langle p_{01}(5-k_5)\rangle,
 &\text{highest}.
\end{array}                                                         \tag{3}
\]
Their linear weighted differences are \(U,U_1\), and the coefficients
of their triangle overlaps remain \(j\). The highest \(H\) term equals
\(H\langle p_{01}(3-s_6)\rangle\), hence it may be kept in any
fraction. The triangle itself gives the exact-reference lower bound
\[
\begin{split}
 2\langle w,L\rangle\ge{}&U_\triangle+\Delta\lambda_1+g\lambda+j\eta\\
 &+H[D_6+2\langle w,z_6\rangle]+R[D_{57}+2\langle w,z_{57}\rangle].
\end{split}                                                         \tag{4}
\]
In detail \(2\langle w,z_6\rangle=3+W^\triangle_6-\langle r s_6\rangle\)
and \(2\langle w,z_{57}\rangle=6+W^\triangle_{57}-\langle r k_5\rangle\).
The matching constants in (4) therefore supply \(H(7-\langle r s_6\rangle)\)
and \(R(14-\langle r k_5\rangle)\). This representation is valid even
at \(a=b\), where no positive price on \(A_4\) alone follows from
the spectral gap.

For \(a=b\) there is a complementary operator identity. Let \(B\) have
the first five eigenvalues all equal to \(a\), the last two \(c,d\).
Inspection of each two-wedge coefficient gives
\[
 L_-(B)=cd\,z_7+(a-c)(a-d)\,z_5+H z_6+R z_{57},\qquad
 z_j=L_-(P_j).                                                       \tag{5}
\]
The first two moments in its triangle polarization are
\(9-\langle r s_7\rangle\) and \(6-\langle r s_5\rangle\), both
nonnegative, since \(s_7\le3,\ s_5\le2,\ \langle r\rangle=3\).
Thus (4) and the approach subtracting \(L_-(B)\) agree after the
omitted nonnegative moments and their corresponding exterior slacks
are accounted for.

## The highest-pair margin and a common Gram correction

On the same physical frame one has
\[
                  d_1\ge\max\{0,L_{01}-2,(L_{01}+L_{02}-4)/2\}.         \tag{6}
\]
The first six-mode edge matching has \(W_1^6\le2\). For the second
bound sum the four vertex degrees of the fixed-pair five-tail
fractional matching over \(2,3,4,5\). The sum is \(L_{01}+W_1^6\le4\).
For the third bound use the complementary triple coordinates of the
usual 98 physical rows. Add the three pair rows \(36,46,56\) and the
five four-set rows \(1345,2346,2356,2456,3456\), all with unit price.
This covers the columns of \(L_{01}+L_{02}+2W_1^6\) at capacity eight.
Columnwise surplus consists just of the complementary triples
\(036,046,056\), each with one surplus cover.

For shifts \(s,t,z\ge0\) on \(u,u_1,w\) respectively, retain the
fraction \(t'/t\), \(0\le t'\le t\), of the highest \(H\) term.
Besides the usual mixed-square terms, equations (3)–(4) then pay the
linear gain
\[
                  24H(s d_s+t'd_1+zD_6)+24zR D_{57}.                  \tag{7}
\]
For a direct simultaneous comparison, bound the cross error using the
original rank-six reserve \(e^2\Psi\beta_6\) with \(e=c-d\),
\(\Psi=e^2+[h^2+q^2+(b-c)^2+d^2]/6\). The single penalty is
\[
 -\frac{144H^2}{e^2\Psi}
 [s^2\kappa+t'^2\kappa_1+z^2\eta+2st'c_1+2sz\lambda+2t'z\lambda_1].
                                                                         \tag{8}
\]
It is zero at \(e=0\). This uses the exact norm of
\(su+t'u_1+zw\) against \(z_6\). For the remaining \(z_{57}\) cross,
\(2\|z_{57}\|^2\le8J_{57}\) by the triangle inequality on its two
Pauli tensor slots. The available \(4(b-c)^2d^2J_{57}\), separate
from all slots in (8), bounds the additional penalty by \(288z^2\eta\)
if \(R>0\), and zero if \(R=0\). Equations (7)–(8) give a signed
alternative to the earlier single-baseline price. The same pure
bottom slots cannot be spent a second time on that baseline.
[Earlier allocation](rank7_six_mode_shared_probe.md)

There is also an independent total-support test. Set
\(\beta_7=2\|z_7\|^2\), \(v=L_{01}-2,\ \nu=L_{01}+L_{02}-4\).
Because \(s_7\le3\), exact polarizations give
\(2\langle u,z_7\rangle\ge\nu\) and \(2\langle u_1,z_7\rangle\ge v\).
Consequently for all nonnegative prices \(l,m\),
\[
 l\nu+mv\le
 \sqrt{\beta_7(l^2\kappa+2lm c_1+m^2\kappa_1)}.                     \tag{9}
\]
The unused pure \(2d^4J_{77}\) pays \(d^4\beta_7\) alongside the explicit
rank-six and rank-five-to-seven allocations of (8). In particular this
allows conversion to a linear support price by completing a square.

## Exact obstruction on the packing relaxation

The factor \(1/2\) in (6) cannot be raised using the 98 rows, all 21
physical \(L_{ij}\le7/3\) caps, and the four nonnegative linear slacks
in (7). A rational example assigns the following *complementary triple*
weights, in units of \(1/4\):

| Triples | Weight in these units |
|---|---:|
| \(016\) | 3 |
| \(034,145,246,356,456\) | 2 |
| \(026,134,135,136,234,235,236\) | 1 |
| every other triple | 0 |

It has \((\nu,v,d_1)=(1/2,1/4,1/4)\), while \(d_s=D_6=D_{57}=0\),
\(x=0\), \(L_{01}+L_{02}+L_{12}=6\), and the total mass inside the
first six vertices is three. The code below verifies all 98 rows, all
21 pair caps, the two columnwise prices, the 232 matching inequalities
and the displayed values in exact arithmetic. This example concerns
the relaxation. Realizability by a seven-frame is open, and the
argument does not prove optimality for the entire \(a=b\) family.
[Exact verifier](../verification/verify_rank7_six_mode_joint_slacks.py)
