# Joint weighted packing with nested compression

November 18, 2026. This comparison uses both mixed probes and the
actual four-wedge compression. Use the notation of the
[two-probe matching proof](rank7_general_two_probe_matching.md).
Let \(E\) be the normalized exterior gain, \(U=W-W_*\) and
\(U_1=W_1-W_{1,*}\) the weighted excesses, \(\nu=L_{01}+L_{02}-4\)
and \(v=L_{01}-2\). Put \(h=\alpha-\beta\), \(k=\beta-\gamma\),
\(q=\gamma-a\), \(g=hq\), \(\Delta=k(\alpha-a)\),
\(R=k^2[k^2+(h^2+q^2)/2]\), and
\[
 G=g-\tfrac{200}{11}b(c-d),\qquad s=G_+,\qquad K=5/2.
\]

The six-mode occupation bound gives
\(2\langle u,L\rangle\ge U+G\kappa+\Delta c_1\).
The reciprocal bound is
\(2\langle u_1,L\rangle\ge U_1+\Delta\kappa_1+g c_1\).
Expanding the single actual norm \(\|L-su-\Delta u_1\|^2\ge0\)
and using \(2sG-s^2=s^2\) gives
\[
 24\|L\|^2\ge
 24sU+24\Delta U_1+12s^2\kappa+12\Delta^2\kappa_1+24\Delta g c_1.
\]
The last term is nonnegative. Adding the independent anticommuting
bound \(2J(C,C)\ge g^2\kappa+R\kappa_1\) and substituting
\(\kappa\ge\nu_+/12\), \(\kappa_1\ge v_+/K\) gives a lower bound
on the combined actual Pauli payment:
\[
 B=24sU+24\Delta U_1+(12s^2+g^2)\nu_+/12+
                   (12\Delta^2+R)v_+/K .
\]
Using signed \(\nu,v\) instead gives a weaker bound. For any
\(0\le\tau\le1\), a sufficient comparison on frames with \(E>0\) is
\(168E\le \tau B+96\mathcal D_F\). This leaves at least a
\(1-\tau\) fraction of the actual Pauli defect. The remaining exterior
gain is piecewise linear in the occupancies and may be checked with
the earlier nested compression certificate. The positive parts can
be incorporated with two epigraph variables in a terminal LP.
[Six-mode correction](rank7_equal_middle.md) ·
[Reciprocal probes](rank7_two_probe_separation_and_tail_region.md) ·
[Compression cells](rank7_residual_nested_compression.md)

## A common choice of spectral threshold

Let \(\mathcal C\) be the wedges containing label 0 and at least one
of labels 1 and 2, and let \(s_{\mathcal C}=\sum_{I\in\mathcal C}w_I\).
The least squared amplitude within this set is \(\alpha\gamma cd\).
Outside it the greatest squared amplitude is
\(\max(\alpha abc,\beta\gamma ab)\), found by choosing the four largest
available probabilities in each of the cases containing and omitting 0.
Thus the whole set is one nested spectral threshold whenever
\(\gamma d>ab\) and \(\alpha cd>\beta ab\). If the gap in amplitudes
is \(\sigma>0\) and packing forces \(s_{\mathcal C}\le3+\rho\) on
\(E>0\) for some \(0<\rho<1\), then
\[
 96\mathcal D_F\ \ge\ 96\sigma^2(1-\rho)(s_{\mathcal C}-3)
\]
on that branch. The right side is nonpositive below trace three.
Above trace three this follows from the fractional spectral rounding
of the threshold. In particular the needed threshold, trace bound,
and compensated objective can be defined without enumerating the
order of every pair of wedge scores. The
[second strictly ordered proof](rank7_joint_single_cut_regression.md)
uses this construction with \(\rho=3/5\) and a rational lower bound
on \(\sigma^2\).

## Rational stress test for the reduced mixed comparison

At \(t=(19.32,4.69,4.13,1.012,1.008,1.004,1)\), interpreted as exact
rationals, one array obeys the original 98 rows and all 21 pair caps.
The [regression verifier](../verification/verify_rank7_combined_payment_regression.py)
lists its entries. It has \(v=\nu=1/3\), \(U_1=30467/93750\),
\(U=29671/93750\), and \(E=40180968947/4687500000\).

A reduced Gram model with only the individual geometric prices permits
\(c_1=0\), \(\kappa=\nu/12\), \(\kappa_1=20v/49\). The latter
already grants a numerically stronger geometry price than proved.
Even granting that model the full \(g\) instead of the lower \(G\),
optimizing both mixed shifts and adding the two anticommuting prices
leaves a deficit of \(373770063497671/11250000000000>33\) in
the comparison with \(168E\). The model drops the actual matching
remainders, joint geometric constraints and compression.

With the proven constants the fixed shifts defining \(B\) leave
less than 93. The compression layer starting at squared amplitude
\(50069229/625000\) has trace \(10/3\) on this array. The one layer
pays more than 388 using the rational bound
\((\sqrt p-\sqrt{p'})^2\ge(p-p')^2/[2(p+p')]\) for neighboring
squared amplitudes. The joint bound therefore covers this array
whether or not a physical frame realizes it.
