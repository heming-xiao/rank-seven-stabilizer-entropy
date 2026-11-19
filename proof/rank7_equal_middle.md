# Rank-seven computational-basis optimality with the second and third probabilities equal

November 18, 2026. Suppose the Schmidt rank is seven and the ordered
probabilities are proportional to \((1,r,r,a,b,c,d)\), with
\(1\ge r\ge a\ge b\ge c\ge d>0\). The descending computational-basis
representative globally minimizes the order-two nonlocal stabilizer
Rényi entropy over arbitrary complex local unitaries, on every qubit
bipartition. Every such spectrum also has a full relative open
neighborhood of rank-seven spectra with the same optimality.

## A weighted comparison valid on one physical frame

Fix an orthonormal frame of Schmidt modes. Write \(E(d)\) for the
four-exterior overlap gain over the sorted reference, normalized by
\(q_F=4/D\), where \(D\) is the ambient dimension. Write \(W(d)\)
for the weighted four-wedge contribution to the mixed polarization
of the two shared-anchor pairs \(01,02\). Let \(U(d)=W(d)-W_*(d)\)
be its difference from the sorted value, and write
\(\nu=L_{01}+L_{02}-4\) for the total unweighted paired excess.
Put
\[
 h=1-r,\quad q=r-a,\quad g=hq,\qquad
 H=g-b(h+3q)-\tfrac52 b^2 .
\]
When \(\nu\le0\), the [forward-gap inequalities](rank7_forward_coefficients_independent.md)
give \(E(d)\le g\,c\,d\,\nu\le0\). The two
exceptional coefficients coincide because the second and third
probabilities are equal. It suffices to consider \(\nu>0\).

At the endpoint \(d=c\), the
[weighted seven-mode packing proof](rank7_equal_floor_weighted_packing.md)
exhibits a nonnegative loss \(B_1\) for this frame with
\[
 U(c)=c^2\nu-B_1,\qquad
 E(c)\le c^2H\nu-(g/2)B_1 .
\]
The four independent forward coefficient losses \(0466,2466,4466,4666\)
lower the relevant gain coefficient from the one using \(c\) to the
one using \(b\). Their bounds are checked in exact rational arithmetic.

At \(d=0\) restrict the same frame to labels \(0,\ldots,5\).
The six-mode weighted endpoint theorem gives
\(U(0)=-B_0\) and \(E(0)\le-(g/2)B_0\), with \(B_0\ge0\).
For a self-contained finite certificate of this step, take the Hodge
complements of the retained four-wedges. The physical edge vector
is in the six-vertex matching polytope by the degree and odd-set rows
of [Sierant, Proposition 10](https://arxiv.org/html/2609.13106v2).
The [rank-six endpoint argument](rank7_two_low_endpoint_interpolation_independent.md)
checks separately the ordinary weighted loss \(B_0\) and the adjusted
loss \(-E(0)-(g/2)B_0\) for every matching. The exact verifier also
checks these two losses by nonnegative forward coefficients on all
76 matchings, including rank-five limits.

Both differences are affine in \(d\) on the same frame. Set
\(S=cd\) and \(B=(d/c)B_1+(1-d/c)B_0\). It follows that
\[
 U(d)=S\nu-B,\qquad E(d)\le S H\nu-(g/2)B,\qquad B\ge0.
\]
Positive gain implies \(H>0\). By \(h+3q\ge2\sqrt{3g}\),
\(H>0\) implies \(g>16b^2\). Indeed if \(x=g/b^2\), then
\(x-2\sqrt{3x}-5/2>0\), which implies \(x>12\) and is impossible
for \(12\le x\le16\). It also follows that \(H<g\), so
\(z=B/(S\nu)\in[0,2)\) when \(E(d)>0\).

## The mixed-sector comparison

Let \(u\) be the mixed projection of the two shared-anchor wedges,
\(\kappa=2\|u\|_{\rm HS}^2\), and \(K=\kappa/\nu\).
The [sharpened shared-anchor estimates](rank7_shared_anchor_twelve_and_anticommuting.md)
give
\[
 K\ge1/12,\qquad \nu\le1/2,\qquad 2J(C,C)\ge g^2\kappa .
\]
The [general conditioned matching bound](rank7_general_two_probe_matching.md)
has reference correction \(b(c-d)\) for unequal last probabilities.
The [six-mode Pauli occupation bound](rank7_four_level_1231_packing.md)
controls the correction by a factor at most \(2\kappa\) for
\(\kappa\le 11/200\), and at most \((200/11)\kappa\)
for \(\kappa\ge11/200\). In detail, it bounds \(\langle p s_6\rangle-5\)
by \( (59/32)\kappa\) in the first regime and by one universally.
Since \(b(c-d)\le b^2-S\) by \((b-c)(b+d)\ge0\), both regimes yield
\[
 2\langle u,L_-(C)\rangle\ge G\kappa+S\nu-B,\qquad
 G=g-\lambda(b^2-S),
\]
where \(\lambda=2\) or \(200/11\) according to the regime.
The actual mixed defect per unit \(\nu\) is therefore at least
\(12(GK+S(1-z))_+^2/K\). The actual anticommuting defect can be
added to this without counting either term twice.

## Small defect

For \(\kappa\le11/200\), \(G=g-2b^2+2S>12S\), and the mixed
bound is nondecreasing in \(K\ge1/12\) at each \(0\le z<2\).
Set \(K=1/12\). Subtracting the gain charge \(168 S(H-gz/2)\)
from the sum of the mixed and anticommuting bounds gives a
function strictly increasing in \(z\). The change in the mixed
term has magnitude at most \(24S(g+12S)<48Sg\), while the
gain charge decreases at rate \(84Sg\). It is enough to prove
\[
 (g-2b^2+14S)^2+g^2/12>168 S H.
\]
After division by \(S\), the left side is decreasing for
\(0<S\le b^2\): its derivative is
\(196-[(g-2b^2)^2+g^2/12]/S^2<0\).
Evaluate at \(S=b^2\). Normalize by \(b^4\), use
\(H/b^2\le x-2\sqrt{3x}-5/2\) with \(x=g/b^2\), and put
\(y=\sqrt{x/3}\). The payment minus the resulting upper bound is
\[
 \tfrac{39}{4}y^4-432y^2+1008y+564
 =164+36(y-4+2/3)^2
   +(y-4)^2\bigl[\tfrac{39}{4}y^2+78y\bigr]\ \ge164 .
\]
This proves strict payment in the small-defect regime.

## Large defect

For \(\kappa\ge11/200\), \(K\ge11/100\) by \(\nu\le1/2\).
It suffices to keep the weaker anticommuting bound \(g^2K/2\)
per unit \(\nu\). With \(\lambda=200/11\) the scalar
comparison is exactly the
[large-defect comparison of the four-level theorem](rank7_four_level_1231.md)
after rescaling an auxiliary flat-tail spectrum. To see this, take
\(P=h+q+b\), \(R=q+b\), and map the old top, middle, tail and floor
ratio to
\[
 1,\qquad R/P,\qquad b/P,\qquad S/b^2.
\]
Here \(P>0\). The old gap and gain coefficient become \(g/P^2\)
and \(H/P^2\) because
\(R(P-R)-(2P+R)b+b^2/2=H\).
The old product of the last two spectral values becomes \(S/P^2\).
The bounds on \(z\) and \(K\) are the same. All payment and gain
terms are homogeneous of degree four, so the previous positive-part
argument and its 34 positive exact Bernstein boxes apply unchanged.
For clarity, that argument minimizes over \(z\in[0,2)\) at \(z=0\),
then over \(K\ge11/100\) at \(K=11/100\). The resulting linear
quantity inside the square is \((11/100)g+3S-2b^2\) and is
bounded below by \(-(6/25)b^2\), as required by the polynomial
certificate. Both regimes leave a strict scalar margin.

## Neighborhoods and validation

At every fixed positive spectrum the two regimes give a positive
margin proportional to \(\nu\) above the upper bound on the gain
whenever \(E(d)>0\). Since \(168E(d)\le168SH\nu\), a uniform
positive fraction of the actual defect can be retained. In the
nonpositive-gain frames all of the defect remains available.
The [strict-margin transfer](rank7_open_interior_neighborhood.md)
now gives a full relative open neighborhood, so the equality of
the second and third probabilities can be split locally. The
two-frame Cauchy–Schwarz comparison and stabilizer padding give the
result on arbitrary quantum cuts.

Run [the exact verifier](../verification/verify_rank7_equal_middle.py) using Python
and SymPy. It verifies the weighted seven-mode duals, 152 six-mode
matching comparisons, 232 unrestricted conditional charges, the
small-defect quartic identity, and the 34 large-defect Bernstein boxes.
[Independent end-to-end review](reviews/rank7_equal_middle_independent_review.md)
