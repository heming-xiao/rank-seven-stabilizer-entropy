# Rank-seven optimality with four equal smallest probabilities

November 18, 2026. Let the ordered positive Schmidt probabilities
have ratios \((\alpha,\beta,\gamma,d,d,d,d)\), with
\(\alpha\ge\beta\ge\gamma\ge d>0\). The sorted computational
representative globally minimizes the order-two nonlocal stabilizer
Rényi entropy over all complex local unitaries on every qubit
bipartition. The three largest probabilities have arbitrary ratios.
Every fixed spectrum in this family also has a full relative open
rank-seven neighborhood with this optimality.

The proof combines two simultaneous mixed shifts, one anticommuting
payment, and two terms from the nested compression inequality.
After the physical reduction, five scalar inequalities are certified
over their whole domains by exact arithmetic.

## Physical comparison with a uniform strict factor

By homogeneity, set \(d=1\). Write \(h=\alpha-\beta\),
\(k=\beta-\gamma\), \(q=\gamma-1\),
\(X=h+k+q\), \(Y=k+q\), \(g=hq\), and \(\Delta=kX\).
Let \(E\) be the normalized exterior gain, \(U\) the weighted
shared-pair difference, and \(U_1\) the weighted highest-pair
difference, all from the sorted reference. Use
\[
 b_*=\frac{101}{100}\,168,\qquad s=\frac54g,\qquad t=\frac54\Delta,
 \qquad\lambda=\frac{24s}{b_*},\qquad\mu=\frac{24t}{b_*}.
\]

For a given frame write \(n=\nu_+\), \(v=(L_{01}-2)_+\),
\(M=\max(n,v/2)\), and \(Z_N=\max(5n/2,2v,2n+v)\).
The [signed packing bound](rank7_three_price_head_expansion.md),
with its third charge set to zero, gives
\[
 E-\lambda U-\mu U_1
 \le (g-\lambda)n+(\Delta-\mu)v-(h+2k+3q)M-Z_N. \tag{1}
\]
In applying that bound, its completion coefficient is
\(XYq-\lambda(Y+q)-\mu q\ge0\).
Indeed \(g(Y+q)+\Delta q\le2XYq\) and the common relative
price is \(24(5/4)/b_*<1/2\). Its geometric price has
\(H\ge3M\), which suffices here. Any remaining signed triangle
term is nonpositive.

Flat tails make the shared mixed coefficient exactly \(g\).
Use the single square for the two shifts \(s,t\). Its cross
coefficient \(s\Delta+tg-st=(15/16)g\Delta\) is nonnegative.
Adding the separate anticommuting term gives a bound on the sum
of the two actual defects \(P_{\mathrm{Pauli}}\):
\[
 P_{\mathrm{Pauli}}\ge24sU+24tU_1+
     \frac{49}{4}g^2\kappa+
     \left(\frac{45}{4}\Delta^2+R\right)\kappa_1,\qquad
 R=k^2\bigl[k^2+(h^2+q^2)/2\bigr].
\]
Here \(\kappa\ge\max(n,v)/12\) and
\(\kappa_1\ge v/(5/2)\).
[Mixed square and pair estimates](rank7_uniform_cut_packing.md) ·
[Independent anticommuting slots](rank7_two_probe_anticommuting.md)

## Two terms of one nested compression inequality

Let \(\mathcal C_1\) be the wedges containing labels 0 and 1,
and \(\mathcal C_2\) the wedges containing label 0 and at least
one of labels 1 and 2. The cuts are nested. For strictly positive
gaps their successive squared-amplitude thresholds in the full
wedge spectrum are \(\alpha\beta\) and \(\alpha\gamma\).
The immediately lower squared amplitudes are respectively
\(\alpha\gamma\) and \(\max(\alpha,\beta\gamma)\).
Therefore both squared adjacent gaps occur in the same
[nested rounding bound](rank7_compression_slack_astra.md). Put
\[
 \sigma_1=\sqrt{\alpha\beta}-\sqrt{\alpha\gamma},\qquad
 \sigma_2=\sqrt{\alpha\gamma}-\sqrt{\max(\alpha,\beta\gamma)}.
\]
For the first cut the trace is \(L_{01}\), whose positive excess
over two is at most \(1/3\). Its term pays
\((2/3)\sigma_1^2 v\). For the second cut the uniform trace
bound, on \(E>0\), gives a term of size at least
\(\omega\sigma_2^2 n\), where
\[
 f=XYq,\qquad \omega=\frac{(f-\Delta/3)_+}{g+2f}.
\]
For zero denominator use zero. To see the trace comparison, the
missing three-head occupancy \(x\) obeys \(2\nu+x\le1\) and
\(E\le g\nu+\Delta (L_{01}-2)-fx\). Thus for \(E>0\) the
second trace is below \(4-\omega\) if \(\omega>0\), with
positive excess over three at least \(n\).
[Uniform trace estimate](rank7_uniform_cut_packing.md)

The two contributions can be added because they are different
summands of the one nested inequality. In particular for \(E>0\),
\[
 96\mathcal D_F\ge64\sigma_1^2 v+96\omega\sigma_2^2 n . \tag{2}
\]
Continuity covers coincident spectral thresholds.

## Rational inequalities for five directions

Let \(L=h+2k+3q\), \(b=1-30/b_*\), and define the scalar base
\[
 B=ML+Z_N+\frac{49g^2}{48b_*}\max(n,v)
       +\frac{(45/4)\Delta^2+R}{(5/2)b_*}v-b(gn+\Delta v).
\]
By (1) and (2) it suffices that
\[
 B+\frac{64}{b_*}\sigma_1^2 v+
       \frac{96}{b_*}\omega\sigma_2^2 n\ \ge0. \tag{3}
\]
The only break directions of this homogeneous piecewise linear
function of \(n,v\) are the axes and \(v/n=1/2,1,2\).
Thus it suffices to use
\((n,v)=(1,0),(1,1/2),(1,1),(1,2),(0,1)\).

If \(L\ge33\), completing squares proves (3) already with the
compression terms discarded. With
\(a_g=49/(48b_*)\), \(a_\Delta=(45/4+1/5)/((5/2)b_*)\)
we have \(b^2/(4a_g)<29,\ b^2/(4a_\Delta)<7\).
Here \(R\ge\Delta^2/5\) by Cauchy--Schwarz.
The resulting debit at each direction is at most
\(29n^2/\max(n,v)+7v\), bounded by \(33M+Z_N\).

For the inner region write \(h=33u_1\), \(k=(33/2)u_2\),
\(q=11u_3\), so the problem lies in the unit cube with
\(u_1+u_2+u_3\le1\). Use the rational square-gap bound
\[
 (\sqrt p-\sqrt r)^2\ge\frac{(p-r)^2}{2(p+r)}
 \qquad(p,r>0).
\]
The first gap contributes at least
\((32v/b_*)\alpha k^2/(\beta+\gamma)\).
For the second, let \(\omega_0=(f-\Delta/3)/(g+2f)\).
If \(\omega_0\ge0\), compare with the minimum of the two
rational square-gap bounds from outside values \(\alpha\) and
\(\beta\gamma\). If \(\omega_0<0\), either signed candidate
is nonpositive and the true compression contribution is
nonnegative. Thus it suffices on any box to certify either the
base plus the first gap, or that same quantity plus each of the
two signed second-gap candidates. The latter candidates are
\[
 \frac{48n}{b_*}\frac{\alpha q(f-\Delta/3)}
                          {(q+2)(h+2XY)},\qquad
 \frac{48n}{b_*}\frac{\gamma h^2(f-\Delta/3)}
                       {(\alpha+\beta)(g+2f)}.
\]
All denominators are positive for strictly positive gaps.

The [standard-library verifier](../verification/verify_rank7_four_equal_tails.py)
reconstructs these polynomials after clearing their positive
denominators. It converts each to tensor Bernstein coefficients
and recursively bisects a longest side at its dyadic midpoint.
At each leaf, nonnegative coefficients prove the required
polynomial inequalities, or the box is certified to have
\(u_1+u_2+u_3\ge1\) and is handled by the square bound.
The checker uses scaled integers, so the signs and subdivisions
are exact. The five trees together have 254 leaves and maximum
depth 17.

## Consequences

On \(E>0\), the physical bound is
\(b_* E\le P_{\rm Pauli}+96\mathcal D_F\), hence at least
\(1/101\) of the actual defect sum remains in the purity comparison.
On \(E\le0\) the exterior term is nonpositive and the full
defects remain. The standard paired reduction and stabilizer
padding give every bipartition. Continuity extends the uniform
margin to leading ties, and the existing strict-margin transfer
gives a full rank-seven neighborhood of each fixed flat-tail
spectrum. [Paired comparison](https://arxiv.org/html/2609.13106v2) ·
[Neighborhood transfer](rank7_open_interior_neighborhood.md)

## A simultaneous continuation away from equal tails

There is a uniform positive tail tolerance for the entire unbounded
flat-tail family. In fact, for the general ordered spectrum
\((\alpha,\beta,\gamma,a,b,c,d)\), retain the definitions
\(h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a\), and set
\(L=h+2k+3q\). The same global optimality holds in either of the
following regions:
\[
 \begin{array}{ll}
 b\le(101/100)d,\quad L\ge35d,&\text{with \(a\) arbitrary in order},\\[1mm]
 a\le(1+\varepsilon_*)d,&
 \displaystyle\varepsilon_*=\min\left\{\frac1{100},
       \frac{\delta(1/37)}{404\cdot19208\cdot7}\right\}.
 \end{array}
\tag{4}
\]
Here \(\delta(s)>0\) is the explicit cutoff in the
[low-defect theorem](rank7_low_defect_interior.md). It has no
ambient dimension factor.

For the first region normalize \(d=1\). The
[general shared mixed bound](rank7_combined_defect_packing.md)
allows \(G=g-\tau\) with \(\tau=(200/11)b(c-1)\).
Take \(s=(5/4)G_+\) and \(t=(5/4)\Delta\), keeping \(b_*\)
and the definitions of \(\lambda,\mu\).
The cross coefficient is \(t g-s\Delta/4\ge0\),
since \(0\le s\le(5/4)g\). The completion coefficient
in the general packing inequality remains nonnegative because
\(\lambda\le30g/b_*\) and \(\mu=30\Delta/b_*\).
With compression omitted, it suffices to certify
\[
 ML+Z_N+
 \frac{(45/4)G_+^2+g^2}{12b_*}\max(n,v)+
 \frac{(45/4)\Delta^2+R}{(5/2)b_*}v
 -(g-\lambda)c\,n-(\Delta-\mu)v\ge0.
\]
The same five directions suffice. At the four directions with
\(n=1\), \(\max(n,v)\le2\), \(c\le101/100\),
and \(\tau\le101/550\). From \(G_+\ge g-\tau\) and
\(G_+^2\ge g^2-2\tau g\), the shared terms together are
bounded below by
\[
 a_g g^2\max(n,v)-\left(\frac{101}{100}b_0+
                   \frac{15}{4b_*}\frac{101}{550}\right)g
 -\frac{1}{20},\qquad b_0=1-\frac{30}{b_*}.
\]
The linear coefficient squared divided by \(4a_g\) is less than
30. At the direction \(n=0\) the entire shared payment is
nonnegative. Completing squares in \(g,\Delta\) therefore leaves
a debit bounded by \(30n^2/\max(n,v)+7v+n/20\), covered
by \(35M+Z_N\) in all five directions. This proves the first
region and retains at least \(1/101\) of the actual Pauli defect.
The verifier checks its rational constants.

For the second region, the first region applies when \(L\ge35d\).
Otherwise set \(d=1\), so
\(\alpha=a+h+k+q<37\), and compare to
\((\alpha,\beta,\gamma,1,1,1,1)\) on the same frame.
Normalize both by the common largest probability \(\alpha\).
They differ by at most \(\varepsilon_*\) coordinatewise and
have normalized smallest probability at least \(1/37\).
The verified flat-tail comparison retains at least \(1/101\)
of the normalized Pauli defect at the reference. For actual
Pauli defect at most \(\delta(1/37)\), use the low-defect
theorem. Above that cutoff, the defect Lipschitz constant
5376 in the [transfer lemma](rank7_open_interior_neighborhood.md)
ensures the flat reference defect is at least half of the actual
defect. In the same lemma the paired-purity difference changes
by at most \(19208\sqrt{37}\,\varepsilon_*\), which is at
most \(\delta(1/37)/404\). The reference's retained margin
pays this change. This completes the second region uniformly in
the three largest probabilities.

A separate [direct unequal-tail certificate](rank7_near_equal_tails.md)
gives the explicit wider tolerance \(a/d\le201/200\) uniformly.

This resolves the full four-equal-smallest pattern, including
three distinct leading probabilities and arbitrary head ratios.
For example \((16,11/2,47/10,1,1,1,1)\) is in this family
and lies outside the earlier [joint sufficient criterion](rank7_leading_split_joint_payment.md)
and [spectral-floor criterion](rank7_spectral_floor_single_probe.md).
General spectra outside the known
regions remain open.
