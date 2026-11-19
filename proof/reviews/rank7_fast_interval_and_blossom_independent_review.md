# Independent audit of the fast interval checker and blossom exclusion

November 18, 2026.

## Equal fifth and sixth probabilities

The C++ implementation and the Python implementation use the same
contractor and the same sufficient inequalities. The C++ fixed-point
unit is \(2^{-27}\). For a positive integer denominator, truncating
division followed by one subtraction on a negative remainder gives
the floor. Negating the floor of the negative numerator gives the
ceiling. On dividing one interval by a positive interval, a negative
lower bound uses the smaller denominator and a negative upper bound
uses the larger denominator. The nonnegative endpoints use the reverse
choices. Products use the four endpoint products. Squaring first
takes the absolute-value interval, giving zero exactly when the
input contains zero.

Signed 64-bit products have absolute value at most \(2^{126}\),
within signed 128-bit range even after negation for a ceiling.
Addition, subtraction, scaling and narrowing of interval endpoints
use checked 128-bit intermediates. Native integer coordinate differences
and midpoint calculations stay within the original range
\(190\cdot2^{27}\). The contractor square root sees a positive
integer at most \(2^{54}\). Floating-point arithmetic supplies
its seed, and both integer correction loops enforce
\(r^2\le v<(r+1)^2\). Floating-point reporting of traversal progress
does not affect the search.

The rate is \(4242/25=(101/100)168\). The reciprocal interval
contains its exact inverse. Multiplying the precomputed reciprocal
or combining repeated terms only changes the interval enclosure,
leaving the pointwise expressions unchanged. This covers the
weighted residual, the two shared modes, both square-root cut
bounds and all six rays. The contractor shrinks only by known
necessary conditions for a point to escape the sufficient tests.
Each split covers its parent with two closed children sharing the
midpoint. Hitting arithmetic overflow, maximum depth or exhausted
dyadic precision exits with failure. A requested partial leaf
limit has a separate exit code, and success requires a drained
work stack.

An independent bounded comparison sent 1,800 exact dyadic points
and boxes through the C++ functions and the Python interval
functions. Both agreed on each outcome: 1,659 outer exclusions,
29 weighted residuals, 44 pure-exterior leaves, 44 tail transports,
one small-shared leaf and 23 joint-price leaves. The full cover
was running separately when this audit was written.
[Fast verifier](../../verification/verify_rank7_equal_fifth_sixth.cpp) ·
[Python verifier](../../verification/verify_rank7_equal_fifth_sixth.py) ·
[Physical comparison and contractor](../rank7_equal_fifth_sixth_candidate.md).

## Saturated blossom and the excluded rational table

For a normalized four-wedge column \(V_I=q_F^{-1/2}\Pi_F x_I\),
let \(b_{ij}\) be the blossom sum with anchor \(i\), omitting \(j\).
Write \(\Psi=\widetilde T_{x_i}^\dagger\Omega\). Then
\(\|\Psi\|^2=q_F b_{ij}\) and
\(\|\widetilde T_{x_i}\Psi\|^2\ge\|\Psi\|^4\). The CAR
decomposition and compressed swap in Propositions 4–5 bound the
square of the antisymmetrized tensor by \(2q_F b_{ij}(2-b_{ij})\).
Testing its one-particle factor against \(\overline{x_j}\) selects
the component \(\Pi_F(x_j\wedge x_i\wedge x_K)/\sqrt{q_F}\).
There is one \(K\) for each unordered triple partition of the six
legs other than \(i\). The wedge shuffle sign is the partition sign
up to a common factor from the position of \(j\). The antisymmetrizer
on two vectors contributes \(\sqrt{2}\) in the unit exterior convention,
so the projected tensor has square \(2q_F\|\mathcal P_i\|^2\).
This verifies the quantitative bound \(\|\mathcal P_i\|^2\le
b_{ij}(2-b_{ij})\) in complex frames.

Independent enumeration of the table yields the three nonzero
partition lists in the proof, with \(b_{06}=b_{36}=b_{46}=2\).
For the three cross marginals \(013/014\), \(023/024\), and
\(015/026\), each triple is saturated and the simultaneous interior
completions are respectively \((2,5),(1,6),(3,4)\).
Their ambient exterior terms vanish by the trace-one identity.
The first two cross equations use
\(V_{0123}\perp V_{0124}\). This orthogonality follows from the
rotatable four-head bound: at fixed \(\nu=1/2\), every unit vector
in the four-tail span has \(w_{012y}\le1/2\).
The \(3,4\) compression has both diagonals \(1/2\) and hence
equals \(I/2\). Independent use of these cross equations gives
\(A\perp B,\ C\perp D'\) and
\(|\langle A,C\rangle|=|\langle B,D'\rangle|\).
The two bases in the plane fixed by the first blossom identity
have diagonal overlaps of equal modulus after normalization.
Their scale factors \(1/2\) and \(1/4\) force both to vanish.
Thus \(C,B,E\) share one line of total mass one, and the positive
contraction forces all other columns perpendicular to it.
The final blossom equation equates a nonzero wedge containing that
line to a wedge entirely in its orthogonal complement.

The quantitative exclusion inherits the same structure. At
coordinatewise error \(\varepsilon=10^{-12}\), the discarded
partitions cost at most \(8\sqrt\varepsilon\) or
\(9\sqrt\varepsilon\) in addition to the \(5\sqrt\varepsilon\)
antisymmetry error. Each cross marginal has outside mass at most
\(4\varepsilon\) per side. The rotated cap bounds
\(|\langle V_{0123},V_{0124}\rangle|\le21\varepsilon\).
These imply the \(26,76,40,192\) constants in the normalized
two-basis argument. Contraction with \(\widehat B\) then controls
the angle of \(C\) to \(B\) by \(516\sqrt\varepsilon\), and the
angle of \(E\) to \(C\) by \(42\sqrt\varepsilon\).
The mass spent in the common line leaves at most
\(360003\varepsilon\) for any other column. The last contracted
left side consequently exceeds \(23/100\), and the right side
plus its error is at most \(1215\sqrt\varepsilon\).
The exact checker also verifies determinant magnitude \(4\) and
inverse infinity norm \(25/4\) of the tight-row matrix, giving
the affine separation on every finite mixture. The corresponding
weak inequality holds on the closed convex hull.
[Proof](../rank7_blossom_gram_witness_exclusion.md) ·
[Exact incidence and constants](../../verification/verify_rank7_blossom_gram_witness.py).

## Triangle defect charged to completion

For the kernel and outside-line ensembles of the leading
three-space, their mean projectors are \(I_3/3\) and \(R\).
The expected product of their two pair deficits is
\(2/3-\operatorname{Tr}R^2+\operatorname{Tr}\rho^2\), where
\(\rho\) is their joint mean tensor. Taking the partial trace
gives \(\operatorname{Tr}\rho^2\ge\operatorname{Tr}R^2/3\).
The pairwise bound of 40 therefore gives
\(1-\operatorname{Tr}R^2\le40\eta\).
For the four-tail projector \(Q\), the rotated exterior bound is
\(QRQ\preceq(1-P)Q\). Hence
\(R^{1/2}QR^{1/2}\preceq(1-P)I\), while the complementary
term has trace \(x\). Therefore
\(\lambda_{\max}(R)\le1-P+x\). With
\(u=(P-x)_+\le1/2\), the purity is at most \((1-u)^2+u^2\), so
\(\eta\ge u(1-u)/20\ge u/40\).

In the signed comparison the triangle baseline difference is
\(-L D_A\), since the only changed completions of a leading
pair are those through the remaining leading leg. Its price
reduces \(C\) by \(24zL/A\) and leaves the separate exterior
triangle coupon intact. With \(C'\ge0\) and
\(0\le z\le\min(j_s,2j_0/13)\), the scalar
\[
  C' b x+q(S-x)_++W(P-x)_+,\quad
  S=(2n+v-3M)_+,\quad
  W=\frac{12z(2j_0-13z)}{40A},
\]
is affine on each segment cut by \(0\le S\le P\). Its minimum
occurs at \(0,S,P\), with values \(qS+WP\),
\(C'bS+W(P-S)\), and \(C'bP\). In the common mixed square, the
extra cross coefficients are proportional to
\(s(j_s-z)+zg\) and \(t(j_s-z)+z\Delta\), both nonnegative.
The old corrected shared mode leaves the pure baseline slots
available for this triangle payment.
[Pairwise bound](../rank7_triangle_quantitative_rigidity.md) ·
[Baseline and completion purity](../rank7_six_mode_shared_probe.md).

## Small second-to-third gap

At \(d=1\), put \(r=k/(bc)\le1/96\). Failure of the pure
comparison requires \(g>(1-2r)bL\), so \(u=h/b,\ z=q/b\)
satisfy \(uz>(47/48)(u+3z)\). For \(H\le0\), the tied base
has nonpositive exterior gain for either sign of the shared
excess. A single highest shift \(t=2\Delta\) leaves coefficient
\(120\Delta\) on \(U_1\le v_+\). The full shared anticommuting
reserve pays \(g^2v_+/12\). For \(H>0\), the shared comparison
uses its existing payment and the remaining half supplies
\(g^2v_+/24\), with the same residual upper bound
\((120kX-168kbc)v_+\). At \(c\ge2\) the harmonic threshold
already applies.

The positive part of the scaled residual before bounding is
\([120r(c/b^2)(u+z+rc-7c/5)]_+\). Using \(1\le c<2\) gives
the two claimed univariate sufficient comparisons. Their
quotient increases in \(u\) throughout the relevant region.
The saturation substitutions are \(z=s(1+w),u=3s(1+1/w)\)
with \(s=47/48\) in the first branch, and
\(z=1+w,u=3+11/(2w)\) in the second. Exact Bernstein verification
passed with two and four leaves. The strict quartics preserve a
fixed-spectrum reserve, including the endpoint \(96dk=bc\).
[Proof](../rank7_small_middle_split.md) ·
[Exact verifier](../../verification/verify_rank7_small_middle_split.py).

## Analytic outer regions and the triangle regression

For the two separated-spectrum comparisons normalize \(d=1\).
Use \(D=1-p(a-c)-(b-1)(c-1)\), \(B=7bc/6\), and \(m=D-B/X\).
Failure of the weighted comparison at \(t=\Delta\), even in the
weak sense, gives
\[
 (122/25)\Delta^2+\max(g^2/24,q^4/72)\le144\Delta m.
\]
At \(k>0\), this forces \(m>0\). Completing the square and then
maximizing \(D/X-B/X^2\) give
\(g<160m,\ q<17\sqrt m,\ k\le (1800/61)D^2/(4B)\).

- If \(c\ge9/5\), the harmonic theorem covers \(c\ge2\).
  On the other part, \(D\le9/25,\ B\ge189/50\), hence
  \(k<13/50\) and pure-exterior failure gives \(q>151/100\).
  For \(X\le12\) we get \(q<4\) and \(X>21/2\).
  For \(X\ge12\) we get \(q<51/5\). Both give
  \(q+151/100<X-k\). With \(r=151/100\),
  \(q(X-k-q)-r(X-k-r)=(q-r)(X-k-q-r)\ge0\).
  AM–GM then requires
  \(2\sqrt{160r(189/50)}<160(9/25)+r(13/50+r)\),
  which the squared rational comparison contradicts.
- If \(b\ge9\), the remaining interval is \(9\le b<21\).
  Indeed pure-exterior failure and the residual bound give
  \(b^2<q^2+4\Delta<21^2\).
  Here \(D\le1,B\ge7b/6\) give \(k<13/(2b)\), so \(q>2b/3\).
  Small-shared failure gives \(h>3bq/(5q-b)>2b/3\), since
  \(q<17\le2b\). With \(s=2b/3\), this yields
  \(g\ge s(X-k-s)\). AM–GM would require
  \(22.3b<160+13/3+4b^2/9\). The opposite difference is
  concave and has endpoint values \(11/30\) and \(3239/30\).
  Both outer arguments therefore preserve a strict margin.

The standard-library verifier passed all 11 rational checks.
[Analytic comparisons](../rank7_separated_bottom_pair.md) ·
[Exact checks](../../verification/verify_rank7_separated_bottom_pair.py).

For the triangle-completion regression, an independent Fraction
calculation used 75 rational bisections for the compression radical.
At the stated spectrum the first cut is inactive, the shared cut is
strict, \(z=j_0/13\), and \(Cb\ge q+W\). Thus the completion price
reduces exactly to \(qS+WP\). With the same first two shifts, the
old comparison has a margin upper bound below \(-1/125\), and
each new ray has a lower bound above \(7/50\). The square term for the
highest shift is \(12t(2\Delta-t)\), as used by the verifier.
The example has \(c/d=1.955\), so it demonstrates a gain of the
triangle comparison within the analytic outer region.
[Triangle comparison](../rank7_triangle_completion_price.md) ·
[Exact regression](../../verification/verify_rank7_triangle_completion_price.py).

On the saturated six-mode face, the only potentially nonzero
outside Pfaffian of \(015\) or \(026\) comes from the pure
three-space \(G\) component. A term with one leg in the
\(J\)-invariant four-space vanishes by that orthogonal block
decomposition. A term with two legs uses \(n,v'\) from different
\(J\)-paired lines and also vanishes. The pure \(G\) volume
has a nonzero completion in \(S^\perp\), because its skew
compression is nonzero and its kernel is sent outside \(G\)
by \(J\). Both saturated triples force the inner kernel and
tail bases to align with their specified two coordinate axes.
Thus \(p_{01}p_{02}=0\) and \(p\,p_{12}=0\) labelwise, giving
\(\kappa=\kappa_{01}+\kappa_{02}\) and
\(\eta=\kappa+\kappa_{12}\). The two individual \(5/2\) bounds
imply \(\kappa,\eta\ge1/5\) on this face at \(\nu=1/2\).
This is a physical necessary condition for its points.
[Face calculation](../rank7_blossom_gram_witness_exclusion.md).
