# Independent review of the unbounded fifth-probability region

November 18, 2026. The comparison proves global order-two sorted
computational-basis optimality for every ordered rank-seven spectrum
with \(b\ge3d\), including the boundary \(b=3d\). The argument is
uniform over the ambient qubit dimensions and complex frames. I
checked both same-frame exterior inputs, the physical payments, and
the two scalar branches. [Proof](../rank7_large_fifth_probability.md).

## Shared-excess cancellation

At \(d=1\) and \(t=\Delta\), the first exterior bound in (2) uses
the signed three-price expansion with only \(\mu=24\Delta/A\).
Its completion coefficient is nonnegative because
\(XY-\Delta=qX\ge0\). Both other weighted probe differences are
bounded by their signed trace coefficients, with the triangle
trace nonpositive. The singleton term is independent of those
three probe deficits. For the second exterior bound, the
same-frame split supplies \(-kbc\,v\) along with its nonpositive
completion term. Its lowered spectrum permits \(E_0\le cHn\)
when \(\nu>0\), and \(E_0\le0\) when \(\nu\le0\).
The actual \(U_1\le v\) follows from the weighted prefix bound.
[Signed comparison](../rank7_low_head_tail_prices.md) ·
[Same-frame split](../rank7_weighted_split_residual.md) ·
[Lowered-spectrum comparison](../rank7_equal_middle.md).

The combination is convex for \(H\le0\) and satisfies
\(\theta g+(1-\theta)H=0\). The singleton contributes
\(\theta bc(2k+h+3q)v/2\). Its \(2k\) part and the split's
\((1-\theta)kbcv\) give a single \(kbcv\) term. Only this combined
upper bound is used. The highest mixed square is still available,
and the two disjoint anticommuting contributions still give
\(R\kappa_1+g^2\kappa\). The inequality
\(5(k^2+h^2/2+q^2/2)\ge(h+k+q)^2\) follows from
Cauchy–Schwarz and yields \(R\ge\Delta^2/5\).
The trace bounds have the signs needed to replace
\(\kappa_1,\kappa\) by \(v/(5/2),v/12\), respectively.
Thus the comparison is valid also at \(v=0\), before division.
[Mixed square and anticommuting allocation](../rank7_leading_split_joint_payment.md).

## Scalar branches and strict margin

For \(H\le0\) the maximum of the left side of (4) is at most
\(\rho^2/(36J)<18/25\). If \(G<13\) the two intervals starting
at \(x=2\) use, in order, concavity and monotonicity of the
positive lower bound \(x(1-13/(x+5/2))/2\) when \(x\ge25/2\).
For \(x\le2\), the bound on \(m\) follows directly from
\[
 \frac{729}{725}\left(w+\frac{25x}{54}\right)^2-w(w+x)
                       =\frac{(4w-25x)^2}{2900}.
\]
The \(H>0\) branch uses the full earlier shared comparison.
Its separate highest residual suffices by (5) at \(t=\Delta\).
The shared proof has already allocated a half of \(g^2\kappa\),
and (5) uses only the other half. At \(k=13/50\) the difference
between the certified right-side lower bound and \(64800/61\)
is \(781/146400>0\), so the tight numerical branch is strict.
The remaining maximum uses \(X<47\). The endpoint and all
other rational comparisons pass the supplied verifier. For
\(H>0\), the existing strict shared reserve and the strict
highest residual control separately \(\nu_+\) and \(v\).
For \(H\le0\), the factor \(A/168=101/100\) gives a uniform
fractional paired margin. These arguments justify the equality
and neighborhood transfer claimed in the theorem.
[Exact verifier](../../verification/verify_rank7_large_fifth_probability.py) ·
[Strict paired margin](../rank7_open_interior_neighborhood.md).

## Exact comparison with prior sufficient tests

The strictly ordered spectrum
\((21.401,6.401,5.501,3.001,3,1.02,1)\) satisfies all
six coarse spectral restrictions listed for the previously
remaining region. Its older optimized highest residual is
\(F=37625078737917/100000000000\), and the previous excess-ratio
sufficiency threshold for \(F\) is \(729/64\). Its highest
compression width vanishes. The pure low-head condition also
fails because \(q+2k/c>b\). These exact comparisons illustrate
the additional reach relative to those particular tests.
[Previous residual](../rank7_weighted_split_residual.md) ·
[Previous excess threshold](../rank7_excess_ratio.md).


## Head-gap region below the fifth-probability threshold

I also verified (6) and (7). Either \(q\le b/2\) or \(h\le3b/2\)
gives \(g\le b(h+3q)/2\), so \(\theta\ge1/2\) and \(H<0\).
The constant coefficient in the signed exterior expansion is
\(\delta N\le-2v\), independently of the singleton coefficient.
The convex combination therefore retains \(2\theta v\) without
reusing any physical defect. The two weighted prices together
give \(1+bc(h+4k+3q)/4\) per \(v\), while the diminished highest
residual is at most \(\rho^2/(4J)<13/2\). Homogeneity restores
the factor \(d^3\) in (6). The strict band (7) comes by applying
the upper bound from each exterior inequality to the one physical
lower bound, with \(D_*\) subtracting \(g^2/(12A)\) per \(v\).
The verified exact example passes all 119 original constraints and
its gains and deficits evaluate as reported. It demonstrates
positive pure exterior gain in the relaxation at a spectrum covered
by the new head-gap theorem.
[Constant and singleton terms](../rank7_low_head_tail_prices.md) ·
[Exact trace bound](../rank7_uniform_cut_packing.md).

