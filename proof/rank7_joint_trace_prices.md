# Joint trace-rounding prices on the two leading cuts

For a physical seven-frame write
\(v=L_{01}-2,\ \nu=L_{01}+L_{02}-4\), and
\(x=1-\sum_{i=3}^6w_{012i}\). The highest cut has trace \(2+v\)
and the shared cut has trace \(3+\nu+x\). The directed and pair
capacities give \(x\ge0,\ 2\nu+x\le1,\ v\le1/3\).
On \(\nu,v>0\) the two fractional trace products therefore satisfy
\[
 \begin{aligned}
 \phi_1&=v(1-v),\\
 \phi_s&=(\nu+x)(1-\nu-x)
        =\nu(1-\nu)+x(1-2\nu-x)\ \ge\ \nu(1-\nu).
 \end{aligned}
\]
Here \(\phi(t)=\{t\}(1-\{t\})\). The shared lower bound
\(\phi_s\ge\nu/2\) applies without a condition on the exterior
gain or the spectrum. The same scalar observation appears in
the earlier four-level proof. It applies to the general
two-cut comparison whenever the shared width is paid.
[Directed capacity and cut trace](rank7_uniform_cut_packing.md) ·
[Earlier four-level application](rank7_four_level_1231_packing.md).

The two true compression intervals are disjoint. In the notation
\(q=\gamma-a\) and \(d=1\) their respective squared endpoints are
\((\alpha\beta c,\alpha\gamma ab)\) and
\((\alpha\gamma c,\max(\alpha abc,\beta\gamma ab))\), listing
the inside and outside endpoints in that order. The highest
outside endpoint is at least the shared inside endpoint. Thus
their simultaneous physical price is
\(96(\sigma_1^2\phi_1+\sigma_s^2\phi_s)\). The same trace
bounds apply to the two nominal widths whenever the crossing
errors have been independently paid.
[Disjoint interval allocation](rank7_crossed_compression.md).

## A finite ratio test stronger than separate linear prices

On the two-positive-excess branch put \(r=v/\nu>0\) and
\(T_r=\min(1/2,1/(3r))\). The two capacity bounds give
\(\nu\le T_r\). The compression terms per unit of \(\nu\)
are thus bounded below by
\[
  96\left[
  \sigma_1^2\,r(1-rT_r)+\sigma_s^2(1-T_r)\right].
\]
For \(r\le2/3\) these price functions are \(r-r^2/2\) and
\(1/2\). For \(r\ge2/3\) they are \(2r/3\) and
\(1-1/(3r)\). Each is concave on its respective interval.
Both directions retain the usual \(2v/3,\nu/2\) linear rates
and improve one of them strictly when its width is positive
and the ratio is away from the common breakpoint.

For the compression-free two-shift margin at fixed spectrum
and shifts, normalize to \(n=1,v=r\). All its terms are affine
on the existing intervals with breakpoints \(1/2,1,2,4\).
Add \(2/3\) to this list before adding the new compression price.
The minimum on each bounded resulting interval occurs at
an endpoint by concavity. The ratio tail \(r\ge4\) is affine
apart from its nondecreasing shared correction, so the rate
at the \(v\)-axis and the value at \(r=4\) suffice. These seven
tests replace the older six tests with constants \(2/3,\omega\).
The same procedure applies to any fixed subinterval of ratios
by adding its two endpoints. In particular, when the proof
uses the independent exclusion \(\ell/F<v/\nu<10g/(bL)\),
one can restrict to that interval for a candidate violating
frame. If a uniform strict paired fraction is needed, the
chosen ratio exclusions and the scalar margin must together
supply that fraction.
[Two-shift margin](rank7_monotone_fifth_gap.md) ·
[Independent ratio exclusions](rank7_excess_ratio.md).

For the strictly ordered spectrum with
\((h,k,q,p,c,b-c)=(14.08,0.95,4.01,0.01,1.05,0.03)\),
use shared and highest shift multipliers \(3/4,7/4\).
Both true widths are positive. With these fixed shifts the
older six-ray price has negative margin on one ray, even using
upper root enclosures. The new ratio price has positive margin
on all seven directions using lower root enclosures. This is
an exact improvement of the sufficient comparison on a fixed
strict spectrum.
[Exact example](../verification/verify_rank7_joint_trace_prices.py).

