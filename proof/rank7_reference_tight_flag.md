# A reference-tight physical flag for the leading pair

For the standard sorted computational seven-frame normalize each
four-wedge weight by \(q_F=4/D\). Its seven nonzero weights are
the affine planes in the coordinate set \(\{0,\ldots,6\}\), each
with weight one. With \(W_{ijk}=\sum_{\ell=0}^6 w_{ijk\ell}\) define
\[
 \begin{aligned}
 E'_0={}&1-w_{0123}-w_{0124}+W_{034}+w_{1234}\\
      &+(1-W_{013})+(1-W_{014})+(1-W_{023})+(1-W_{024}),\\
 E'_f={}&E'_0+(1-W_{015})+(1-W_{026}).
 \end{aligned}                                                       \tag{1}
\]
Both are nonnegative affine functions of the physical four-wedge
weights and both vanish at the standard computational frame. In
every ambient qubit dimension,
\[
 \begin{aligned}
 \langle p\,p_{12}\rangle&\le45 E'_0,\\
 \langle p_{01}p_{02}+p\,p_{12}\rangle&\le1560 E'_f,\\
 \eta&\ge\kappa+\kappa_{12}-90E'_0,\\
 \eta&\ge(2/5)\nu+\kappa_{12}-3120E'_f,\\
 \max(0,L_{01}-2,L_{02}-2)^3 &\le 2\cdot10^{14} E'_f .
 \end{aligned}                                                       \tag{2}
\]
The signed Gram inequalities in (2) are affine inequalities on the
joint moment relaxation. They are tight at the computational frame.

## Localizing the four-Pfaffian

In the [pointwise argument](rank7_saturated_face_exclusion_and_stability.md)
the full \(d_0=\sum_{i<j<k\in Y}|F(0,i,j,k)|^2\) is used solely
to bound the magnitude of \(F(x_0,t_q,\ell,v')\). The two vectors
\(t_q,\ell\) form an orthonormal basis for \(Q=\operatorname{span}(x_3,x_4)\),
and \(v'\) is a unit vector in \(V=\operatorname{span}(x_5,x_6)\).
Alternation followed by Cauchy–Schwarz gives the tighter bound
\[
 |F(x_0,t_q,\ell,v')|^2
   \le |F(x_0,x_3,x_4,x_5)|^2+|F(x_0,x_3,x_4,x_6)|^2 .
\]
The right-hand side, averaged over skew Pauli labels, equals
\(3T_*\) for \(T_*=w_{0345}+w_{0346}\). All later inequalities,
including the [general cubic argument](rank7_physical_flag_cubic_cut.md),
use \(d_0\) through this estimate or its resulting total error.
Thus every proof holds with \(T_*\) in place of \(T_Y\), with the
same constants. Observing that \(T_Q+T_*=W_{034}+w_{1234}\) gives
(1). The standard four-sets supporting the computational weights are
\(0123,0145,0246,0356,1256,1346,2345\). They give all the claimed
zero slacks directly. These elementary incidences are included in
the [exact checker](../verification/verify_rank7_saturated_face_separation.py).

One may also retain the pointwise factor \(p\) against this localized
sum: the only use in the regular branch is multiplied by \(p\) when
bounding \(p d_n^2\). This refinement leads to a joint Pauli moment
in place of \(T_*\); (1) uses only the measured exterior weights.

## Why rotating the earlier flag cannot make it tight

The compression of \(q_F^{-1}\Pi_F\) to the seven-dimensional
computational support in degree four is the diagonal projector on
the seven affine four-sets listed above. Each plane has its own
direction within this support, since its parallel mate within the
eight-point cube contains the omitted vertex. The one-particle
and two-particle marginals of this projector are \(4I\) and \(2I\),
by the \(2\)-(7,4,2) incidence counts. Their expectations are
therefore constant under **every** unitary change of basis within
the seven-space, even if it mixes all three proposed heads with
all proposed tails.

For any orthonormal frame in that support let \(D_0=\sum_{I\ni0}w_I\)
and \(A_i=w_{012i}\). Inclusion–exclusion gives
\[
        T_Y=D_0-L_{01}-L_{02}+\sum_{i=3}^6 A_i.
\]
The marginal identities give \(D_0=4,\ L_{01}=L_{02}=2\) in every
basis, so
\[
     (1-A_3-A_4)+T_Y=1+A_5+A_6\ge1 .
\]
In particular the earlier raw flag cannot be made reference-tight by
permutation or rotation, even with full freedom in the seven-space.
The restriction to \(\Lambda^2Q\wedge V\) bypasses exactly that
obstruction.

## Consequences for homogeneous comparisons

Writing \(v_i=L_{0i}-2\), (2) supplies supporting rows
\(2\cdot10^{14}E'_f\ge 3t^2v_i-2t^3\) for \(0\le t\le1/3\).
On the whole exposed face \(E'_f=0\) the two separate inequalities
\(v_1\le0,\ v_2\le0\) follow. The derivative of the cubic at the
reference is zero. Thus positive directions with \(E'_f>0\) may
remain feasible after scaling down toward the reference; the cubic
alone gives no first-order price on such directions. Equations (2)'s
two signed Gram inequalities do give first-order comparisons of the
Pauli and packing quantities without a computational-reference constant.
The remaining spectrum comparison requires prices for those quantities.
