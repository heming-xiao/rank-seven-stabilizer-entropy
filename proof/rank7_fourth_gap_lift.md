# An exterior deficit from the gap after the fourth Schmidt probability

November 18, 2026. Let the ordered Schmidt probabilities be proportional to
\(\alpha,\beta,\gamma,a,b,c,d\). On every qubit bipartition the sorted
computational representative globally optimizes the rank-seven problem if
\[
                    (a-b)(\gamma-b)\ge cd.                         \tag{1}
\]
The result follows from the exterior contribution alone. In particular
the entire family with \(b=c=d\) and \(a\ge2d\) satisfies the comparison,
with arbitrary first three probabilities. A sharper test is (7) below.
For three equal smallest probabilities the additional condition
\(\gamma-a\ge4d/5\) also suffices, at every fourth probability. Its
proof transports the previously certified computation at \(a=d\).
This proof uses the existing physical packing inequalities for the actual
frame and the established nonpositivity of the ordinary forward
coefficients. [Forward coefficients](rank7_forward_coefficients_independent.md)

## Four-head incidences

Normalize \(d=1\) throughout the proof. Set \(H=\{0,1,2,3\}\),
\(w=w_{0123}\), \(f=1-w\). For each triple \(S\subset H\), write
\(W_S=\sum_{I\supset S}w_I\), \(m_S=W_S-w\), and \(e_S=1-W_S\).
Every \(e_S\ge0\) by the complement four-set row. The three complement
pair rows indexed by \(45,46,56\) give exactly
\[
                  3w+\sum_{S\subset H,\ |S|=3}m_S\le3,
          \qquad \sum_{|S|=3} e_S\ge f.                         \tag{2}
\]
Indeed the complement of \(H\) contains three low pairs, the complement
of a wedge with three high labels contains one, and all other complements
contain none. If \(T_i=\sum_{I\ni i}w_I\) and
\(L_{ij}=\sum_{I\supset\{i,j\}}w_I\), then
\[
                  T_i\le4,\qquad
                  R_i=\sum_{j\in H\setminus\{i\}}L_{ij}\le6
                  \quad(i\in H).                               \tag{3}
\]
Summing the six directed rows which contain \(i\) and omit another
label counts each four-wedge through \(i\) three times and gives the first
bound. Summing only the three rows omitting a low label counts that same
wedge \( |I\cap H|-1\) times and gives the second. Both inequalities
are equalities at the reference, where every pair total is two and
every three-head triple is completed by \(H\).

Define \(v=L_{01}-2\) and \(\nu=L_{01}+L_{02}-4\). The same physical
rows give
\[
                        \max(0,v,\nu)\le f.                      \tag{4}
\]
For \(L_{01}+w\le3\), add the complement four-set rows on
\(2456,3456\) and the complement pair row on \(23\). Every complement
with neither (0) nor (1) is covered, and \(456\), the complement of
\(H\), is covered twice. For \(L_{01}+L_{02}+w\le5\), use the directed
row whose complement contains (3) and omits (0) and the three low
pair rows. A wedge containing both \(0,1,2\) is covered twice, with a
third cover when it equals \(H\). A wedge containing (0) and exactly
one of \(1,2\) is covered by the directed row if it omits (3), and by
a low pair row otherwise.

## A comparison on a fixed physical frame

First impose \(b=c=d=1\). Define \(X=\alpha-a,Y=\beta-a,Z=\gamma-a\),
\(p=a-1\), \(y=(X,Y,Z,0)\), and \(P_i=p+y_i\). Let \(E(p)\) denote
the actual-minus-reference normalized exterior gain, with the same
frame and \(y\) throughout the path. Every wedge weight equals
\(\prod_{i\in I\cap H}(1+P_i)\). Expanding in the subsets of \(H\)
and subtracting the expansion at \(p=0\) gives
\[
\begin{split}
 E(p)-E(0)={}&p\sum_{i\in H}(T_i-4)
   +p\sum_{i\in H}y_i(R_i-6)
   +\tfrac12p^2\sum_{i\in H}(R_i-6)\\
 &-\sum_{|S|=3}\left(\prod_{i\in S}P_i-\prod_{i\in S}y_i\right)e_S
   -pP_0P_1P_2 f .
\end{split}                                                       \tag{5}
\]
The triple products on the second line have increments at least
\(pP_1P_2\). For \(S=012\), subtracting \(pP_1P_2\) leaves
\(X[(Y+p)(Z+p)-YZ]\ge0\). For the other three triples this is
immediate from the order. Applying (2) and (3) proves
\[
   E(p)\le E(0)-P f,\qquad
   P=p(1+p+X)(p+Y)(p+Z).                                         \tag{6}
\]

For general tails still normalized by \(d=1\), set \(p=a-b\) and keep
\(X,Y,Z\) and all other forward gaps fixed when defining \(E(0)\).
The polynomial \(E(p)-E(0)\) consists of all forward monomials
containing the gap at index three. Every such coefficient is
nonpositive because the five exceptional index multisets are
\(0166,0256,0266,1166,1266\). Discard terms also containing index
four or five. What remains is exactly the difference in (5), with
\(y=(X,Y,Z,0)\) and the three lowest probabilities all set to one.
Thus (6) holds without any tail equalities.

Set \(g=(X-Y)Z\) and \(\Delta=X(Y-Z)\). The ordinary two-pair forward
bound at \(p=0\) reads \(E(0)\le cg\nu+\Delta v\).
Combining with (4) gives the explicit sufficient condition
\[
                    P\ \ge\ cg+\Delta.                           \tag{7}
\]
For (1), normalization gives \(p(p+Z)\ge c\ge1\). It implies
\(P\ge cXY\ge cg+\Delta\), using \(g+\Delta=Y(X-Z)\le XY\).
Consequently \(E(p)\le0\). The published upper comparison then yields
computational-basis optimality, including arbitrary complex local frames.

## Simultaneous subtraction of the three mixed probes

In this subsection \(b=c=d=1\). For the ordered nested probe families
\(\{01,02\},\{01\},\{01,02,12\}\), choose prices
\(0\le\lambda\le g,\ 0\le\mu\le\Delta,\ 0\le\zeta\le YZ\).
Their edge coefficients are \(c_{01}=\lambda+\mu+\zeta\),
\(c_{02}=\lambda+\zeta\), \(c_{12}=\zeta\), so
\(0\le c_{ij}\le y_i y_j\). Write
\(F(p)=E(p)-\lambda U(p)-\mu U_1(p)-\zeta U_\triangle(p)\).
For any leading edge \(e=ij\) let \(k\) be its other leading label
in \(\{0,1,2\}\). Its individually weighted probe has exact variation
\[
     U_e(p)-U_e(0)=-p(e_{ij3}+e_{ijk})-p(p+y_k) f .
\]
This follows by expanding the product of the two unoccupied slots in
the probe. In (5), each triple \(ij3\) therefore retains the price
\(p(P_iP_j-c_{ij})\). The price on \(012\), divided by \(p\), is
\(p^2+p(X+Y+Z)+\sum_{i<j\le2}(y_i y_j-c_{ij})\), at least the smallest
of the other three prices. Hence (2) gives
\[
 F(p)\le F(0)-p f\left[P_0P_1P_2-
               \sum_{ij\subset\{0,1,2\}}c_{ij}P_k+
               \min_{ij\subset\{0,1,2\}}(P_iP_j-c_{ij})\right].    \tag{8}
\]
For instance, if \(c_{ij}\le\theta y_i y_j\) with \(0\le\theta\le1/3\),
the bracket is bounded below by
\[
 (1-3\theta)XYZ+(1-\theta)YZ
 +p[(1-\theta)(XY+XZ+YZ)+Y+Z]+p^2(X+Y+Z+1)+p^3 .
\]
The positive deficit in (8) is available alongside the previously
proved mixed and anticommuting estimates. [Three weighted probes](rank7_three_price_head_expansion.md)

## Two threshold intervals through all spectral crossings

Continue with \(b=c=d=1\). In the ordered spectrum of wedge
amplitudes \(\sqrt{\prod_{i\in I} t_i}\), consider the intervals
\[
 [l_s,u_s]=[\sqrt{\max(\alpha a,\beta\gamma)},\sqrt{\alpha\gamma}],
 \qquad [l_1,u_1]=[\sqrt{\alpha\gamma},\sqrt{\alpha\beta}].
\]
The basic shared cut contains wedges with (0) and at least one of
\(1,2\); its trace is \(s_s=3+\nu+x\) with \(x=1-W_{012}\).
No wedge outside it can have amplitude above \(l_s\), apart from
the three wedges \(123i\) with \(i=4,5,6\), all at amplitude
\(\sqrt{\beta\gamma a}\). All its included amplitudes are at least \(u_s\).
Likewise the highest-pair cut contains \(01\) and has trace
\(s_1=2+v\); its only external groups above \(l_1\) can be
\(023i\) and \(123i\), at \(\sqrt{\alpha\gamma a}\) and
\(\sqrt{\beta\gamma a}\). Every promoted group has reference mass
zero and actual mass \(m_S\le f\).

Split each interval at its interior exceptional amplitudes. For each
open component of length \(h>0\) use the upper spectral cut of any
interior point. Its trace is \(s_{\mathrm{base}}+m\), where \(m\) is
the total mass of promoted groups above the interior point, including
groups above the upper endpoint. This gives the physical estimate
\[
 \mathcal D_F\ge \sum_{\rm components}h^2
            \phi(s_{\mathrm{base}}+m)
     +(\sqrt{\alpha\beta\gamma a}-\sqrt{\alpha\beta\gamma})^2 f(1-f),
 \qquad \phi(z)=\{z\}(1-\{z\}).                                 \tag{9}
\]
The two intervals have disjoint interiors. The last term is the
single-wedge top cut, also disjoint since \(\gamma\ge1\). If two
components belong to the same true spectral gap, their squared
lengths sum to at most that gap squared. Thus (9) follows by summing
distinct terms in the nested compression inequality, without spending
the same squared gap twice. [Compression and fractional trace](rank7_compression_slack_astra.md)

The largest shared subgap is at least \((u_s-l_s)/2\), and the largest
highest-pair subgap at least \((u_1-l_1)/3\). For a price in the
original observables one can replace each fractional-trace factor by
\([\phi(s_{\rm base})-m]_+\), by periodic one-Lipschitz continuity.
On \(E(p)>0\), (6) and the original forward triple price give
\(E(p)\le g\nu+\Delta v-XYZ x-P f\). Since \(x\le f\), the old
uniform shared-trace proof applies with \(F=XYZ+P\), giving
\(\phi(s_s)\ge[(F-\Delta/3)_+/(g+2F)]\nu_+\), with zero assigned
at a zero denominator. For the highest-pair cut
\(\phi(s_1)\ge(2/3)v_+\). These inequalities retain the
mass penalty when an external group has crossed a threshold.
The pure test (7) and the compression estimate (9) leave a residual
region when the fourth gap is small, both probes have positive prices,
and the external masses are appreciable. [Uniform trace estimate](rank7_uniform_cut_packing.md)

## An analytic continuation uniform in the fourth probability

For \(b=c=d=1\) the sorted representative is globally optimal at every
\(p\ge0\) whenever \(Z=\gamma-a\ge4/5\). By (1) we only have to study
\(0\le p\le1\). Apply the flat-tail theorem on the same frame at \(p=0\),
with \(b_*=(101/100)168\), \(\theta=30/b_*\), and the two physical shifts
\(s=5g/4,t=5\Delta/4\). Their packing prices are
\(\lambda=\theta g,\ \mu=\theta\Delta,\ \zeta=0\). Both \(g,\Delta\)
are constant along this lifting path. The mixed lower bound with these
same shifts is valid for every \(p\), since its shared matching gap is
\(G=g\) when the three lowest weights equal one. The two anticommuting
lower bounds \(g^2\kappa+R\kappa_1\), with
\(R=(Y-Z)^2[(Y-Z)^2+((X-Y)^2+Z^2)/2]\), are also unchanged. Thus the
only possible decrease in the flat theorem's scalar deficit payments is
the loss of its two lower bounds for physical compression. The strict
factor comparison is used on \(E(p)>0\); (6) implies \(E(0)>0\) there.
[Flat-tail payment and its scalar certificate](rank7_four_equal_tails.md)

In (8) the bracket is nondecreasing in \(p\). Indeed the first term
minus the sum has linear coefficient \(\sum_{i<j}(y_i y_j-c_{ij})\ge0\)
and nonnegative quadratic and cubic coefficients. Each term inside
the minimum is also nondecreasing. At zero this bracket equals
\[
 B_0=YZ[1+(1-2\theta)X+\theta(Y+Z)]
      \ \ge\ (1-2\theta)(1+X)YZ.                                  \tag{10}
\]
Here \(P_1P_2-c_{12}=YZ\) is the minimum at zero since \(c_{12}=0\),
\(c_{02}=\theta(X-Y)Z\), and \(c_{01}=\theta Y(X-Z)\). Therefore the
packing gain has decreased by at least \(p B_0 f\).

Let \(\sqrt U,\sqrt W\) be the smallest inside and largest outside
amplitudes at zero for either of the flat theorem's two cuts. Each
outside wedge has at most three of the upper four labels. At most one
of these contributes the ratio \(\sqrt{1+p}\). The other ratios are
at most \(\sqrt{1+p/(1+Z)}\). Hence every outside amplitude increases
by a factor at most
\[
 \sqrt{1+p}\left(1+\frac p{1+Z}\right)
 \ \le\ 1+Cp,\qquad C=\tfrac12+\frac{3}{2(1+Z)} .
\]
This bound also covers a wedge containing only the first three heads,
because the largest allowed ratio is \(\sqrt{1+p}\). Inside amplitudes
only increase. Write the available gap of this same cut at \(p\) as
zero if it has ceased to be an upper threshold cut. Its squared gap
can fall by at most \(2Cp\sqrt W(\sqrt U-\sqrt W)\), by
\(t^2-(t-u)_+^2\le2tu\).

For the highest-pair cut the last quantity is
\[
  2Cp(1+X)[\sqrt{(1+Y)(1+Z)}-(1+Z)]
     \le Cp(1+X)(Y-Z).
\]
For the shared cut it is at most \(Cp(1+X)(1+Z)/2\), by
\(\sqrt W(\sqrt U-\sqrt W)\le U/4\). When both available gaps are
positive they come from nested cuts, so their payments still add;
a lost gap has zero payment. The flat theorem paid the respective
squared gaps with \(64v_+\) and \(96\omega\nu_+\), \(0\le\omega\le1/2\).
Its original trace estimates still hold because the frame is unchanged
and \(E(0)>0\). Using (4), the total compression payment lost is at most
\[
 Cp(1+X)[64(Y-Z)+24(1+Z)]f
 \ \le\ 64Cp(1+X)Y f\qquad (Z\ge3/5).                              \tag{11}
\]
For \(Z\ge4/5\) we have \(C\le4/3\) and
\((b_*-60)Z\ge(2742/25)(4/5)>256/3\).
Consequently \(b_*pB_0 f\) from (10) covers (11). Applying the certified
flat-tail scalar comparison yields the claimed result for every \(p\).
