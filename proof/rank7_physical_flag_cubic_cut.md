# A physical convex cut for each leading edge

For a physical seven-frame define \(v_i=L_{0i}-2\) for \(i=1,2\).
Let \(E_f=A_0'+T_Q+T_Y+C_Q+C_*\) be the nonnegative affine
flag error defined in (2) of the [face stability note](rank7_saturated_face_exclusion_and_stability.md).
In every local qubit dimension,
\[
          2\cdot10^{14} E_f\ \ge\ \max(0,v_1,v_2)^3 .              \tag{1}
\]
In particular \(E_f=0\) forces both pair values to be at most two.
This conclusion requires only the raw flag constraints. It applies
throughout the flag face, independently of any prescribed value of
the packing objective or the other six-mode deficits.

## Selecting labels for both edges

Use the local notation in the [pointwise estimate](rank7_saturated_face_exclusion_and_stability.md).
The three discarded branches of that estimate have \(p\le128\xi\),
where \(\langle\xi\rangle=3E_f\). On its regular branch
\(\delta\le1/4\) assign the label to orientation 1 if \(s\ge1/2\)
and to orientation 2 otherwise. The orientation error \(B\) satisfies
\[
     p\delta^2\le8\xi,\qquad
     p^2B\le(4/3)p(\sqrt e+4\sqrt3\,\delta)^2
             \le(4/3)(1+384)\xi.
\]
For orientation 1 one has \(1-s\le B,\ t'\le2B\). For orientation
2 one has \(s\le B,\ 1-t'\le2B\). These inequalities follow directly
from \(B=st'+(1-s)(1-t')\). Consequently the wrong edge has weight
at most \(pB\). The line comparison preceding (7) in the face note
gives projection distance
\(d_{\rm im}\le\sqrt{2}\,\delta+\sqrt{2B}\) of \(JQ\) from its
assigned two-plane (\(Q_A\) or \(Q_B\)). Thus
\[
                     p^2 d_{\rm im}^2\le2100\xi.
\]
For any \(0<\epsilon\le1\), retain labels of each orientation
with \(d_{\rm im}\le\epsilon\); denote the two sets by \(A,B'\).
For each edge on its deleted regular labels, \(p_i^2\le2100\xi/\epsilon^2\):
use the projection bound if the distance is too large, and
\((pB)^2\le p^2B\) on the other orientation. The normalized
number of regular labels is at most 16 by the rank-four Pauli twirl
in the face note. By Cauchy–Schwarz their deleted \(p_i\)-mass
is at most \(\sqrt{16\cdot2100\cdot3 E_f}/\epsilon\). The three
other branches cost at most \(128\cdot3 E_f\). Hence each retained
set carries normalized mass at least \(1-l\), where
\[
                    l=384E_f+318\sqrt{E_f}/\epsilon.                 \tag{2}
\]

## One positive edge suffices

Fix an edge \(0i\) of positive excess \(\mu=v_i\le1/3\). Assume
\(E_f\le\mu^3/(2\cdot10^{14})\) and set
\(\epsilon^2=\mu/160000\). Then (2) gives \(l<\mu/100\).
Indeed \(l/\mu\le384/(9\cdot2\cdot10^{14})+
318\sqrt{160000/(2\cdot10^{14})}<1/100\).
Both retained sets are nonempty. The set for the positive edge
has cardinal at least \(D(1+\kappa_i-2l)/2\) and hence
\[
                |A_i|>{D\over2}(1+0.38\mu),                       \tag{3}
\]
because \(\kappa_i\ge(2/5)\mu\) by the individual Pauli bound.

Translate each retained set by one of its own elements and take the
union \(T\). Its labels move \(Q\) by at most \(2\epsilon\). As
in the face note, \(|10T|\le2D/(1-400\epsilon^2)<4|T|\). The
strict inequality follows from
\((1+0.38\mu)(1-400\mu/160000)>1\) on \(0<\mu\le1/3\).
Therefore \(\langle T\rangle=8T\). Group averaging and spectral
rounding yield a rank-two \(Q_*\) with \(\|Q-Q_*\|\le32\epsilon\),
invariant under \(\langle T\rangle\). The full preserving group
\(H\) of \(Q_*\) has \(|H|\ge D\) by (3). As proved in the face
note, its symplectic rank is two and \(|H|=D\) or \(2D\).
Every retained set is contained in a single \(H\)-coset.

The plane \(Q_*\) belongs to one block of the radical \(R_H\).
Each antiunitary with label in a fixed \(H\)-coset has the same
action on radical characters. Choose any label in the retained
set for the *other* edge. Its image of \(Q_*\) has projection
distance at most \(33\epsilon\) from the corresponding assigned
plane, which contains \(x_i\). Thus \(x_i\) has squared leakage
\(e_i\le(33\epsilon)^2\) outside a particular radical block \(U\).
The positive edge's coset maps \(U\) to one other fixed block \(U'\),
allowing equality.

- If \(|H|=D\), radical blocks have rank four. The strict odd
  majority (3) forces \(q(r)+[a,r]=0\) for every radical element
  \(r\), since otherwise odd and even labels split that coset
  equally. Therefore the positive edge's coset fixes every
  radical block and \(U'=U\).
- If \(|H|=2D\), the blocks have rank two. Two distinct blocks of
  the same radical are jointly contained in a rank-four stabilizer
  block, by restricting both characters to the kernel of their
  nontrivial quotient. A single rank-two block is also contained
  in a rank-four block, by dropping one generator.

In both cases there is a rank-four stabilizer block \(D_4\)
containing \(U+U'\).

## Converting retained mass to a pair bound

Let \(e_0=\|(I-P_{U'})x_0\|^2\). On the retained set \(A_i\),
every \(J_a\) maps \(U\) onto \(U'\) and \(U^\perp\) onto
\((U')^\perp\). Thus the two crossed terms vanish in
\(\langle x_0,J_a x_i\rangle\). Triangle inequality in normalized
square sum and skew Parseval on each of the remaining terms give
\[
       \sqrt{1-l}\le
       \sqrt{(1-e_0)(1-e_i)}+\sqrt{e_0e_i}.                         \tag{4}
\]
Use planar unit vectors \((\sqrt{1-e},\sqrt e)\).
Their angle difference has sine at most \(\sqrt l\) by (4),
so \(\sqrt{e_0}\le\sqrt{e_i}+\sqrt l\) and
\(e_0\le2(e_i+l)\).
The [near-affine-four pair inequality](rank7_shared_anchor_twelve_and_anticommuting.md)
applied to \(D_4\) now gives
\[
   \mu\le18(e_0+e_i)\le18(2l+3e_i)
      <18\left({2\over100}+{3\cdot33^2\over160000}\right)\mu<\mu.
\]
This contradiction proves (1), including a strict comparison for
positive individual excess. All explicit rational comparisons in
this note and the fixed face-distance calculation are checked by
the [standard-library verifier](../verification/verify_rank7_saturated_face_separation.py).

## Using the cut in an optimization

For any \(t\in[0,1/3]\), each of the following inequalities is
affine in the 35 wedge weights and valid on their closed convex hull:
\[
     2\cdot10^{14} E_f\ge 3t^2 v_i-2t^3,\qquad i=1,2.              \tag{5}
\]
The cubic is the supremum over these supporting lines, with the
positive part implemented by \(t=0\). In computations one may
evaluate the nonnegative summands of \(E_f\) directly. Its upper
envelope \(3A'_0+2(1-2\nu-x)+(2d_1-\nu)\) from the face note also
gives valid, weaker cuts. The inequalities extend to role
permutations of the seven labels. No assumption of spectral
degeneracy enters the proof.
