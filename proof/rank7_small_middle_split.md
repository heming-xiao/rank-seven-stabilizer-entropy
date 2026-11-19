# A uniform second-to-third gap in rank-seven spectra

November 18, 2026. Let \((\alpha,\beta,\gamma,a,b,c,d)\) be any
positive descending rank-seven Schmidt spectrum, up to scaling.
The sorted computational representative globally minimizes the
order-two nonlocal stabilizer Rényi entropy over all complex local
unitaries and all qubit bipartitions whenever
\[
                         96\,d(\beta-\gamma)\le bc. \tag{1}
\]
In particular \(\beta-\gamma\le d/96\) suffices regardless of the
other six probabilities. The endpoint in (1) is included.
Every such fixed positive spectrum admits a positive paired-defect
margin, so the [equality classification](rank7_all_tie_equalities.md)
and unrestricted local spectral neighborhood apply there. The result
does not require any four-wedge spectral threshold or compression
payment.

## Two branches of the tied-middle transport

Normalize \(d=1\), and let \(h=\alpha-\beta,\ k=\beta-\gamma,\
q=\gamma-a,\ X=h+k+q,\ L=h+2k+3q,\ g=hq,\ \Delta=kX\).
The case \(k=0\) is the [tied-middle theorem](rank7_equal_middle.md).
For \(c\ge2\) use [harmonic-tail transport](rank7_harmonic_tail_transport.md).
Now suppose \(c<2,\ k>0\), and set \(r=k/(bc)\le r_0=1/96\).

The weighted singleton price gives
\[
 E\le cg\,n+\Delta v-bcLM,\qquad M=\max(n,v/2),
\]
where \(n,v\) are the positive parts of the shared and highest-pair
trace excesses. Thus \(g\le(1-2r)bL\) implies pure exterior
optimality, since \(\Delta=kX\le kL\). Only
\(g>(1-2r)bL\) needs further treatment. [Exterior coupons](rank7_low_head_tail_prices.md)

Let \(H=g-b(h+3q)-(5/2)b^2\). A sufficient condition in the
remaining branch is
\[
 \begin{array}{ll}
 g^2/12\ge120kX-168kbc,& H\le0,\\
 g^2/24\ge120kX-168kbc,& H>0.
 \end{array} \tag{2}
\]
To see the second line, apply the
[weighted split residual](rank7_weighted_split_residual.md) with
highest-pair shift \(t=2\Delta\). Its right-hand side is at most
\(120\Delta-168kbc\): the normalized five-tail discount is at most
one, and the completion term is nonpositive there. The disjoint
half of the shared anticommuting slots pays at least \(g^2v/24\).
All other residual payments may be omitted. The established shared
comparison still uses its assigned mixed shift in the same square.

For the first line, lowering the first two entries by \(k\) on the
same frame gives a tied-middle base with nonpositive exterior gain
\(E_0\) on both signs of the shared trace excess: its signed bound is
\(E_0\le cH\nu-gB_0/2\) for \(\nu>0\), and \(E_0\le cg\nu\)
for \(\nu\le0\). No shared physical payment is required. The split
inequality gives \(E\le\Delta U_1-kbc\,v\), with \(v\) still the
positive part. The sole mixed shift \(t=2\Delta\) therefore pays
\(48\Delta U_1\) in physical units. The remaining coefficient
\(120\Delta\) multiplies \(U_1\le v\), and the entire shared
anticommuting price is now available. It is at least \(g^2v/12\).
[Same-frame split](rank7_highest_pair_split_loss.md) ·
[Anticommuting reserve and shared frame bound](rank7_uniform_cut_packing.md)

## Reduction to two one-variable quartics

Let \(u=h/b,\ z=q/b,\ s=1-2r_0=47/48\).
Failure of the pure comparison implies \(uz>s(u+3z)\). Hence
\(z>s,\ u>3s\).
We have \(X/b=u+z+rc\le u+z+2r_0\) and \(c/b^2\le1\).
The positive part of \((120kX-168kbc)/b^4\) is therefore at most
\[
                120r_0(u+z+2r_0-7/5)_+ .
\]
Indeed before taking the positive part the exact expression is
\(120r(c/b^2)(u+z+rc-7c/5)\).
For the two branches of (2) it suffices to prove
\[
 (uz)^2 > m r_0(u+z+2r_0-7/5),\quad
                  m=1440\text{ or }2880. \tag{3}
\]
For positive denominator the quotient
\((uz)^2/(u+z+2r_0-7/5)\) increases in \(u\), since
\(u+2z+4r_0-14/5>0\) throughout this region. A nonpositive
denominator is harmless.

For \(H\le0\), use only \(uz\ge s(u+3z)\). At fixed \(z\) the
lowest permitted \(u\) is represented by
\(z=s(1+w),\ u=3s(1+1/w)\), \(w>0\).
For \(H>0\), the stronger \(uz>u+3z+5/2\) gives boundary
\(z=1+w,\ u=3+11/(2w)\). Substitution in (3) gives the two
quartics
\[
 Q(w)=w^2[(uz)^2-m r_0(u+z+2r_0-7/5)] .
\]
For example \(8Q(w)=72w^4+168w^3+213w^2-572w+242\)
on the second boundary. The [exact verifier](../verification/verify_rank7_small_middle_split.py)
constructs both quartics from the two substitutions, compactifies by
\(w=y/(1-y)\), and verifies strictly positive Bernstein coefficients
after dyadic subdivision. The first branch uses two leaves at depth
one, and the second uses four leaves at depth three.

Thus (2) holds strictly whenever the pure branch has not already
finished the proof. On a positive-gain frame with \(v=0\), the
shared proof retains its original strict margin; when \(H\le0\)
such a frame cannot occur. At a fixed spectrum a strict residual
margin times \(v\), together with the existing per-spectrum strict
shared comparison, retains a positive fraction of the actual
defects just as in the weighted split theorem. The paired reduction,
stabilizer padding and spectral transfer give every claimed cut and
neighborhood. [Paired transfer](rank7_open_interior_neighborhood.md)

