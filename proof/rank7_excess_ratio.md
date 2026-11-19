# Necessary excess ratios for a rank-seven counterexample

November 18, 2026. At arbitrary ordered positive rank-seven
Schmidt probabilities \((\alpha,\beta,\gamma,a,b,c,d)\),
each paired frame with either nonpositive leading excess has
purity at most the sorted computational value. The same
argument gives an exact interval for the ratio of excesses
on any remaining candidate frame. If this interval is empty
the spectrum is globally optimal on every qubit cut.

Use \(h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a,\ p=a-b\),
\(X=h+k+q,\ L=h+2k+3q,\ g=hq,\ \Delta=kX,\ S=cd\).
The signed trace excesses are
\(\nu=L_{01}+L_{02}-4\) and \(v_1=L_{01}-2\).
Put \(n=\nu_+\) and \(v=(v_1)_+\).

## Two physical frame conditions that suffice for every spectrum

The [small-shared proof](rank7_small_shared_gain.md) uses
\(5g\le bL\) only to obtain \(5g n\le bL\max(n,v/2)\).
The rest of that proof, including the six-variable compact
certificate with an independent \(q\) coordinate, therefore
applies to any paired frame satisfying the latter inequality.
In particular this covers \(\nu\le0\). It retains the \(1/101\)
paired defect margin at all such frames.
[Existing exact checker](../verification/verify_rank7_small_shared_gain.py).

For the other axis, compare to the actual frame with the
first two probabilities lowered by \(k\). Write \(E_0\) for
that exterior gain and \(E\) for the actual gain. Use
\(D_A\) for the completion deficit and set \(O=E_0-kgD_A/2\).
The transfer identity is \(U=U_0-kD_A\) for the shared
weighted probe. If the auxiliary highest gain \(U_1^0\le0\),
then \(U_1=U_1^0-qD_A\le-qD_A\) in the actual spectrum.
The highest split gives \(E-E_0\le\Delta U_1\le-kgD_A\).
Thus \(E\le O\), and the old actual shared square and the
anticommuting reserve already pay \(O\).
This covers \(v_1\le0\) because the auxiliary prefix bound
gives \(U_1^0\le d^2v_1\).
More generally the same comparison applies whenever the
full highest residual
\[
 \Delta U_1-kbcd\,v-kq(q+3a-b-c-d-h/2)D_A
\]
is nonpositive. [Split identity](rank7_highest_pair_split_loss.md) ·
[Actual shared transport](rank7_harmonic_tail_transport.md).

Any positive paired purity gain therefore requires
\(\nu>0\), \(v_1>0\), \(U_1^0>0\), and
\[
                  \frac{v_1}{\nu}<\frac{10g}{bL} .
 \tag{1}
\]
The ratio follows because
\(5gn>bL\max(n,v/2)\). A two-sided counterexample would
need at least one violating paired frame by the Cauchy–Schwarz
reduction. This conclusion concerns the frames, including in
the presence of spectral ties.

## The reserve gives the opposite bound

Let \(H=g-b(h+3q)-(5/2)b^2\).
If \(g=0\) use the small-shared theorem, and if \(\Delta=0\)
use the tied-middle theorem. Otherwise define
\[
 \ell=\begin{cases}
 g^2/24,&H\le0,\\
 \min\{g^2/24,\ell_s,\ell_l\}, &H>0 ,
 \end{cases}
\]
where
\[
\begin{aligned}
 \ell_s&=(g-2b^2+14S)^2+g^2/24-168SH,\\
 \ell_l&=12[(11/100)g+3S-2b^2]_+^2/(11/100)
                +(11/200)g^2-168SH.
\end{aligned}
\]
Both scalar surpluses are strictly positive on \(H>0\)
by the existing tied-middle bounds with one half of the
leading anticommuting payment. In detail, for \(\nu>0\),
if \(O>0\) then \(H>0\) and its upper bound is
\(S\nu(H-gz/2)\) for \(z=(S\nu-U)/(S\nu)\in[0,2)\).
The shared minimum occurs at \(z=0\) and \(K=\kappa/\nu\)
equal to \(1/12\) or \(11/100\) in the two regimes.
The first uses uniform tail loss \(2(b^2-S)\),
the second \((200/11)(b^2-S)\). Substitution gives the
two displayed strict prices. If \(O\le0\), use zero shared
shift and the half reserve \(g^2\kappa/2\ge(g^2/24)\nu\).
Thus the physical shared payment always exceeds \(168O\)
by at least \(\ell\nu\) when \(\nu>0\).
[Tied-middle scalar proof](rank7_equal_middle.md) ·
[Half-reserve transport](rank7_leading_split_joint_payment.md).

Let \(F\) be the right minus left side of equation (1) of the
[tail-weighted highest residual](rank7_weighted_split_residual.md)
with its exact optimal \(t\). The shared shift and highest
shift use one mixed square with nonnegative cross term,
and the highest comparison still has the unused half
anticommuting reserve and its independent compression price.
Consequently the actual purity gain is at most
\(F v-\ell\nu\) whenever \(\nu>0\).
If \(F\le0\) the earlier weighted residual already gives
global optimality. Otherwise a violating frame must obey
\[
                    \frac{\ell}{F}<\frac{v_1}{\nu}
                                     <\frac{10g}{bL}.             \tag{2}
\]
In particular the explicit spectral condition
\(\ell bL\ge10gF\) is sufficient, including the case \(F>0\)
where the weighted highest residual alone was inconclusive.
The paired reduction gives the two-sided statement.
With a strict spectral inequality the estimate
\(Fv-\ell\nu\le(10gF/(bL)-\ell)\nu\) on the remaining cone,
and \(E\le c d g\,\nu+d^2\Delta v\), give a positive
per-spectrum paired margin. The already covered cone retains
its original margin, so strict spectra have an optimal
neighborhood and local Clifford equality.

For a strictly ordered example set \(d=1\) and take
\((h,k,q,p,b,c)=(12.42,0.0464,1.88,0.327,1.181,1.039)\).
Here \(H<0\) and the actual highest amplitude gap is zero.
Exact rational evaluation shows \(0<F<1/10\) and
\(\ell bL/(10g)>2\), so (2) is impossible even though the
weighted residual is positive. The former small-shared
condition and the pure low-head test both fail at this point.
[Exact example checker](../verification/verify_rank7_excess_ratio.py).

