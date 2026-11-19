# A uniform 0.5 percent tail region for rank seven

November 18, 2026. Let \((\alpha,\beta,\gamma,a,b,c,d)\) be any
ordered positive rank-seven Schmidt spectrum satisfying
\[
                         a\le (201/200)d .
\]
Then the sorted computational representative minimizes order-two
nonlocal stabilizer Rényi entropy over arbitrary complex local
unitaries on every qubit bipartition. There is no restriction on the
ratios of the first three probabilities. The inequality permits
all seven probabilities to differ. Each spectrum in the region has
a uniform paired defect margin, including when the tail ratio is
at its stated endpoint.

The [flat-tail proof](rank7_four_equal_tails.md) already supplies
the unbounded branch \(h+2k+3q\ge35d\) whenever \(b\le101d/100\).
For the remaining branch the following rational bounds validate
the entire tail interval at once, with only three spectral variables
in the Bernstein subdivision.

## Mixed and exterior bounds uniform in the tails

Set \(d=1\), \(u=201/200\), and let \(h=\alpha-\beta\),
\(k=\beta-\gamma\), \(q=\gamma-a\), \(X=h+k+q\), \(Y=k+q\),
\(g=hq\), and \(\Delta=kX\). Use \(b_*=(101/100)168\),
\(G=g-(200/11)b(c-1)\), \(s=(5/4)G_+\), and \(t=(5/4)\Delta\),
with \(\lambda=24s/b_*,\mu=24t/b_*\). As in the unbounded
continuation, the mixed cross coefficient is nonnegative.
Set \(n=\nu_+\), \(v=(L_{01}-2)_+\), \(M=\max(n,v/2)\), and
\(Z_N=\max(5n/2,2v,2n+v)\). Write
\(r_0=1-30/b_*\), \(\tau=(200/11)u(u-1)\). The signed packing
with third charge zero has completion coefficient
\(C=XYq-\lambda(Y+q)-\mu q\ge(9/14)XYq\).
Its geometric term is
\(3M+\theta(2n+v-3M)_+\), with
\(\theta=\min(1,aC/q)\) for \(q>0\).
An extra \(q(2n+v-3M)_+\) is therefore available wherever
\(9XY\ge14\).

Start with the normalized difference between the mixed and
anticommuting payments and the exterior charge. First substitute the
geometric bound \(\kappa\ge\max(n,v)/12\) into the nonnegative
sum \(g^2+(45/4)G_+^2\). Next use
\(G_+^2\ge g^2-2\tau g\) and \(G_+\ge g-\tau\).
In the signed exterior difference the remaining shared coefficient
is at most \(u(r_0g+30\tau/b_*)n\), and the highest-pair
coefficient is \(r_0\Delta v\). Thus a sufficient comparison
uses the conservative base
\[
 \begin{split}
 B_0={}&(h+2k+3q)M+Z_N+
  \frac{(49/4)g^2-(45/2)\tau g}{12b_*}\max(n,v)\\
 &+\frac{(45/4)\Delta^2+R}{(5/2)b_*}v
     -u(r_0g+30\tau/b_*)n-r_0\Delta v ,
 \end{split}
\]
where \(R=k^2[k^2+(h^2+q^2)/2]\).
[Uniform signed packing](rank7_three_price_head_expansion.md) ·
[Mixed and anticommuting comparison](rank7_uniform_cut_packing.md)

## Lower bounds for the two nested compression gaps

The highest-pair cut has lower inside score \(p_1=\alpha\beta cd\)
and upper outside score \(r_1=\alpha\gamma ab\).
The shared cut has \(p_2=\alpha\gamma cd\) and
\(r_2=\max(\alpha abc,\beta\gamma ab)\).
Whenever either gap is positive the corresponding cut contributes
its term in the nested compression bound. If both are positive the
two terms occur in disjoint adjacent spectral gaps, as the two cuts
are nested and \(p_2\le r_1\). When a cut is unseparated assign its
contribution zero.

Write \(j=u^2-1\). Subtracting the paired scores gives
\[
 p_1-r_1\ge\alpha[k-j(u+q)],\quad
 p_2-\alpha abc\ge\alpha c(q-j),\quad
 p_2-\beta\gamma ab\ge\gamma[h-j(u+k+q)] .
\]
The positive-gap price obeys the rational square-gap inequality in
the flat-tail proof. Use \(x^2-2xy\le(x-y)_+^2\) for \(x,y\ge0\),
and upper-bound the score-sum denominators with \(a,b,c\le u\).
This gives these signed lower bounds for the squared gaps:
\[
 \frac{(1+X)k[k-2j(u+q)]}{2u^2(2u+k+2q)},\qquad
 \frac{(1+X)q(q-2j)}{2(u+q+u^2)},\qquad
 \frac{(1+q)h[h-2j(u+k+q)]}{2u^2(2u+h+2k+2q)}.
\]
The first is for the highest-pair cut. The minimum of the last
two bounds the shared cut. A negative signed bound is valid by
nonnegativity of the corresponding actual term. If both shared
bounds are positive, both outside endpoints lie strictly below
the inside threshold, so the shared cut is available.

As before, the first cut pays at least \(64v\) times its bound in
the actual purity comparison. For the second, put \(f=XYq\).
The uniform trace cutoff uses the ratio
\(\omega=(af-\Delta/3)_+/(cg+2af)\), which is at least
\((f-\Delta/3)_+/(ug+2f)\). This follows from monotonicity in
\(af\) and \(cg\). On any box where \(f-\Delta/3\ge0\),
we can therefore add \(96n\) times the signed lower candidate
for each shared gap times the latter ratio. If either candidate
is negative, the physical shared payment is still at least the
minimum of the two signed candidates. Consequently the two
candidate comparisons, taken together, suffice. Dividing by
\(b_*\) gives the polynomial numerators used by the verifier.

## Exact coverage and strict margin

The remaining \(h+2k+3q\le35\) region lies in the nonnegative unit
cube after \((h,k,q)=(35u_1,(35/2)u_2,(35/3)u_3)\).
The six directions are \((1,0),(1,1/2),(1,1),(1,2),(1,4),(0,1)\).
They cover every breakpoint of \(M,Z_N,\max(n,v)\) and the
optional geometric term. On each dyadic box the verifier proves
the base plus highest-pair comparison, or proves both shared
alternatives with their required sign. The extra geometric term
may be used after certifying \(9XY\ge14\) on that same box.
Clearing the positive denominators and testing nonnegative
Bernstein coefficients certifies each accepted box. The six
trees have 266 leaves and maximum depth 14. At vanishing gaps
the comparison follows by continuity of the physical inequality.
[Standard-library verifier](../verification/verify_rank7_near_equal_tails.py)

Thus \(b_*E\) is paid by the actual Pauli and compression
defects on \(E>0\), preserving a fraction \(1/101\) of their sum.
For \(E\le0\) the defects are nonnegative. The paired reduction,
stabilizer padding and strict-margin transfer give the stated
theorem and relative open neighborhoods of fixed spectra.
[Paired purity](https://arxiv.org/html/2609.13106v2) ·
[Strict-margin transfer](rank7_open_interior_neighborhood.md)
