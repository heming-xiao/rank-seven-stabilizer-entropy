# Independent review of the raw flag cubic bound

November 18, 2026.

The dimension-independent bound
\[
 E_f\ge \frac{\max(0,L_{01}-2,L_{02}-2)^3}{2\cdot10^{14}}
\]
holds for all physical seven-frames. The proof below checks the
selection, group, and terminal estimates for one positive edge.
It uses the raw affine observable \(E_f\) independently of the
packing gain or the other six-mode deficits.
[Main proof](../rank7_physical_flag_cubic_cut.md).

## Normalized mass removed by orientation

Use the regular branch of the previously audited pointwise flag
estimate, with skew mass \(p=p_{01}+p_{02}\), squared flag
error \(\xi\), and angle-error quantities \(\delta,B\).
It gives \(p\delta^2\le8\xi\) and
\(p^2B\le(1540/3)\xi\).
Writing \(s=p_{01}/p\) and using
\(B=st'+(1-s)(1-t')\), the wrong edge for the orientation
chosen at \(s=1/2\) has mass
\(p\min(s,1-s)\le pB\).
Comparing the two images of the core with the assigned plane
gives \(d_{\mathrm{im}}\le\sqrt2\delta+\sqrt{2B}\).
Consequently
\[
 p^2d_{\mathrm{im}}^2\le4p^2(\delta^2+B)
                 \le(6256/3)\xi<2100\xi .
\]
For a discarded regular label, either its image distance
exceeds \(\epsilon\), or it belongs to the other orientation.
In both cases its deleted edge mass satisfies
\(p_i^2\le2100\xi/\epsilon^2\), since \(B\in[0,1]\) and
\(\epsilon\le1\). This lets the two cases use one normalized count.

The regular label count is at most \(16\) in normalized skew
measure. Indeed each image of \(Q\) in that branch has trace
at least \(2-2\delta^2\ge1\) on \(M+V\). The full Pauli
twirl sums that trace to \(8D\), and the normalized count uses
factor \(2/D\). As \(\langle\xi\rangle=3E_f\), Cauchy–Schwarz
gives deleted regular mass at most
\(\sqrt{16\cdot2100\cdot3}\sqrt{E_f}/\epsilon
<318\sqrt{E_f}/\epsilon\).
The irregular branches have \(p_i\le128\xi\), contributing
at most \(384E_f\). Thus deletion for either edge costs at
most \(l=384E_f+318\sqrt{E_f}/\epsilon\).
[Pointwise flag and twirl](../rank7_saturated_face_exclusion_and_stability.md).

## A large support from one positive edge

Fix \(\mu=L_{0i}-2>0\) and assume
\(E_f\le\mu^3/(2\cdot10^{14})\).
With \(\epsilon^2=\mu/160000\) and \(\mu\le1/3\),
\[
 l/\mu \le \frac{384}{18\cdot10^{14}}
            +318\sqrt{\frac{160000}{2\cdot10^{14}}}<1/100.
\]
Both retained supports are nonempty by their remaining mass
\(1-l\). Only the positive edge needs a large support. Its
individual Pauli defect satisfies \(\kappa_i\ge(2/5)\mu\).
Since \(p_i+p_i(1-p_i)\le1\), its ordinary count exceeds
\((D/2)(1+0.38\mu)\).

Translate each support by one of its own labels and take their
union \(T\). The product estimate and the twirl give
\(|10T|\le2D/(1-400\epsilon^2)<4|T|\).
The strict comparison follows by expanding
\((1+(19/50)\mu)(1-\mu/400)>1\).
A length-nine shortest path would supply four disjoint
translates of \(T\) indexed by prefixes \(0,3,6,9\) in \(10T\).
An intersection would shorten their separation to at most
two. Hence the group generated is \(8T\). Averaging and Weyl
rounding give an invariant rank-two \(Q_*\) within \(32\epsilon\)
of \(Q\). Its full projective Pauli group has order \(D\) or
\(2D\) and symplectic rank two, as in the audited exact face proof.

Each support lies in a single coset of this group. Take any
label in the other support. Its image of \(Q_*\) lies in a
radical character block \(U\) within leakage \(33\epsilon\)
of the assigned plane containing \(x_i\). In particular
\(e_i=\|(I-P_U)x_i\|^2\le(33\epsilon)^2\).
All labels of the positive edge map \(U\) to a common block \(U'\).
If the group has size \(D\), the majority of odd points in the
positive-edge coset forces its radical shift to be trivial,
so \(U'=U\) is four-dimensional. If it has size \(2D\),
the two blocks are jointly contained in a four-dimensional
stabilizer subspace. For distinct characters, restrict them
to the kernel of their relative character; if they coincide,
drop one radical generator.

## Parseval on the two blocks and final bound

Let \(e_0=\|(I-P_{U'})x_0\|^2\). For labels of the positive
support, \(J_a U=U'\), so the crossed matrix elements between
the blocks and their complements are zero. Apply the triangle
inequality in normalized square sum to the two same-block
terms. Complete skew Parseval on either term gives
\[
 \left\langle|\langle x,J_a y\rangle|^2\right\rangle
     =\|x\|^2\|y\|^2-|\langle x,y\rangle|^2
     \le\|x\|^2\|y\|^2
\]
for arbitrary (possibly nonorthogonal) projected vectors.
This yields
\[
 \sqrt{1-l}\le\sqrt{(1-e_0)(1-e_i)}+\sqrt{e_0e_i}.
\]
For the two real unit vectors with coordinates
\((\sqrt{1-e_j},\sqrt{e_j})\), the sine of their angle
difference is at most \(\sqrt l\). Decomposing the first
vector into the second and its orthogonal line gives
\(\sqrt{e_0}\le\sqrt{e_i}+\sqrt l\).
Hence \(e_0\le2(e_i+l)\).
The established rank-four stabilizer bound applies to
the subspace containing both blocks, so
\[
 \mu\le18(e_0+e_i)
       \le18(2l+3e_i)
       <18(2/100+21/1000)\mu
       =(369/500)\mu .
\]
The last step uses \(33^2/160000<7/1000\).
This contradiction proves the cubic bound, strictly when
the tested edge has positive excess. At zero excess the
bound follows from \(E_f\ge0\). Eight rational comparisons
were recomputed independently, including the deleted-mass
constants, the group-cardinality gap, and the final margin.
[Fixed rank-four pair bound](../rank7_shared_anchor_twelve_and_anticommuting.md).

For a closed-convex-hull proof, each supporting line
\(3t^2 v_i-2t^3,\ 0\le t\le1/3\), is an affine constraint
against \(2\cdot10^{14}E_f\). Its validity survives mixing
and closure across ambient dimensions. Equality of the raw
flag forces each individual excess to be nonpositive.

## Tightness at the computational reference

The only place the pointwise proof uses \(d_0\) as the norm
of an error is in bounding \(F(x_0,t_q,\ell,v')\).
The orthonormal vectors \(t_q,\ell\) span \(Q\), so their
two-wedge is \(x_3\wedge x_4\) times a unit phase.
Because \(v'\) is a unit vector in \(\operatorname{span}(x_5,x_6)\),
the Cauchy–Schwarz bound is
\[
 |F(x_0,t_q,\ell,v')|^2
    \le |F(x_0,x_3,x_4,x_5)|^2+
         |F(x_0,x_3,x_4,x_6)|^2 .
\]
The phase and, in the complex convention, conjugation of the
coefficients leave the norm bound unchanged. Thus the latter
sum can replace \(d_0\). Its mean is \(3T_*\), where
\(T_*=w_{0345}+w_{0346}\). The early \(d_t,d_v\) branches
use only the unaffected errors \(a,b,c\). The retained proof of
\(p\delta^2\le8\xi_0\) then gives the same \(128\) constant
on the third bad branch. The orientation and deletion constants
are unchanged, so the cubic holds with
\(E_f^{\rm tight}=A'_0+T_Q+T_*+C_Q+C_*\).

At the computational reference, \(w_{0123}=1\), \(T_Q=0\),
and \(T_*=0\). The six saturated completion rows \(013,023\),
\(014,015\), and \(024,026\) are completed within the support
by \(0123,0145,0246\), respectively. Hence the tightened
observable has value zero there. The original \(T_Y\) has
value one from \(0356\). The same supporting affine cuts
therefore apply with a left side that vanishes at the
computational reference.
[Pointwise argument](../rank7_saturated_face_exclusion_and_stability.md).
