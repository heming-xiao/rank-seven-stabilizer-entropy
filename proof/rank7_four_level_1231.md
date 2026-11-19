# Computational-basis optimality for rank-seven \(1+2+3+1\) spectra

November 18, 2026. For every \(1\ge r\ge s\ge w>0\), the sorted
computational representative of a pure qubit state with Schmidt
probabilities proportional to \((1,r,r,s,s,s,w)\) minimizes the
order-two nonlocal stabilizer Rényi entropy on its full local-unitary
orbit, on every bipartition. Every such spectrum also has a full
relative open neighborhood of rank-seven spectra with the same
optimality, allowing all seven probabilities to become distinct.

## Exterior and mixed quantities along the lowest leg

Fix a frame of seven orthonormal Schmidt modes and use normalized
four-wedge occupations \(q^{-1}\|\Pi_F u_I\|^2\), \(q=4/d\).
Write \(E(w)\) for the normalized exterior-overlap gain over the
sorted reference, and let \(W(w)\) be the mixed polarization's
weighted exterior sum for the two shared-anchor pairs \(01,02\).
A four-wedge containing all three leading modes is counted twice
with the product of the middle and tail probabilities for the
remaining pair. A four-wedge containing the highest and exactly
one middle mode is counted once with the product of its two
remaining tail probabilities.

Let \(A,B\) be the total occupations of those two blocks. Set
\(\nu=2A+B-4\) and \(x=1-A\). The
[three-level packing proof](rank7_three_level_124_packing_and_scalar.md)
gives \(x\ge0\) and, when \(\nu>0\), \(\nu\le1/2\),
\(x\le1-2\nu\). At \(w=s\), that proof also gives
\[
 E(s)\le s^2H\nu-s(1-s)(r-s)^2x,\qquad
 W(s)-W_{\rm CB}(s)=s^2\nu-2s(r-s)x,
 \qquad H=r(1-r)-(2+r)s+s^2/2.
\]

At \(w=0\) use the six-mode space with labels \(0,\ldots,5\).
Write \(A_0,B_0,C_0,D_0,E_0\) for the occupations of the
four-wedges in this space, ordered by \((\text{highest included},
\text{number of middle modes})\) as
\((1,2),(1,1),(1,0),(0,2),(0,1)\).
Their computational reference occupations are \((1,1,0,0,1)\).
With the six-mode Hodge complement, the relevant normalized
occupations satisfy the matching-polytope degree, triangle and
five-set inequalities. Specifically \(A_0\le1\) by the triangle
on the three bottom labels, and \(A_0+B_0+C_0\le2\) by the
five-set omitting the highest label. Put
\[
 x_0=1-A_0,\qquad z_0=2-(A_0+B_0+C_0),\qquad
 B_0=1+x_0-z_0-C_0.
\]
The degree at the highest label gives \(D_0+E_0\le1\).
The bottom degree sum gives \(2A_0+B_0+D_0\le3\), hence
\(D_0\le x_0+z_0+C_0\).
The reference for \(W(0)\) is \(2rs+s^2\), so
\[
 m_0=W_{\rm CB}(0)-W(0)=(2rs-s^2)x_0+s^2(z_0+C_0)\ge0 .
\]
The actual endpoint exterior-overlap gain is
\[
 r^2s(A_0-1)+rs^2(B_0-1)+s^3 C_0
       +r^2s^2D_0+rs^3(E_0-1).
\]
Substitute the highest degree bound first, then the bottom
degree bound with multiplier \(rs^2(r-s)\ge0\). This yields
\[
 E(0)\le-rs(r-s)(1-s)x_0-rs^2(1-r+s)z_0-s^2g C_0
       \le-\tfrac12g m_0,\qquad g=(1-r)(r-s).
\]
For the last step, \(r(1-s)\ge(2r-s)(1-r)/2\) and
\(r(1-r+s)\ge g\). The six-mode inequalities used here are the
physical matching rows in [Sierant, Proposition 10 and Theorem 8](https://arxiv.org/html/2609.13106v2).

Now both \(E(w)\) and \(W(w)-W_{\rm CB}(w)\) are affine in \(w\)
when the frame is fixed. Put \(v=w/s\) and
\[
 U=sw\nu,\qquad B_*=2v s(r-s)x+(1-v)m_0.
\]
The \(x\)-loss at \(w=s\) is at least \(g/2\) times its
polarization loss, since \(1-s\ge1-r\). Consequently
\[
 E(w)\le UH-(g/2)B_*,\qquad W(w)-W_{\rm CB}(w)=U-B_* .
\]
If \(\nu\le0\), the
[forward coefficient bound](rank7_forward_coefficients_independent.md)
directly gives \(E(w)\le gsw\nu\le0\). This follows since
\(b_1=0\), \(b_0b_2=g\), and \(t_5t_6=sw\).

## Mixed payment and a single separated compression block

The [three conditional matching maxima](rank7_three_level_124_conditional_matching.md)
stay unchanged for this split spectrum. With a highest–middle edge
the maximum \(M_1\) is \(r+rs+s^2\), with a middle–middle edge it is
\(r^2+s+s^2\), and with no leading edge it is \(s+2rs\).
Each maximum has a matching using only the three tails of probability
\(s\). The computational weighted exterior sum decreases to
\(W_{\rm CB}(w)=2rs+s^2+sw\). Accounting for this change requires a
six-mode matching charge.

On each skew Pauli, let \(p=p_{01}+p_{02}\), \(m=p_{12}\), and
\(s_6=\sum_{0\le i<j\le5}p_{ij}\). Let \(\langle\cdot\rangle\)
denote the \(2/d\)-normalized sum over skew Pauli labels. Write
\(s_{C(w)}\) for the weighted sum of all seven-label edges on the
same Pauli. On any matching of \(k\) edges, suppose \(\delta=1\)
if the lowest vertex is used and \(0\) otherwise. The best matching
in its leading-edge class at \(w=s\) exceeds its flat score by
at least \((3-k)s^2\). With a fixed leading edge one can add
unused edges. In the class with no leading edge the only case with
\(k<3\) and no permitted addition has two tail–tail edges covering
all four tails. Replace one by two leading–tail edges; the net
increase is at least \(2rs-s^2\ge s^2\). The weight of a matching
using the lowest vertex decreases by at least \(s(s-w)\) when
lowering \(w\). Since \(k-\delta\) counts edges within the first
six modes, the pointwise loss from the class maximum is at least
\(s(s-w)(3-k+\delta)\).
The [exact verifier](../verification/verify_rank7_four_level_1231_scalar.py)
also enumerates all 232 matchings and confirms this inequality
by coefficientwise comparison in the nonnegative gaps. Applying
the matching decomposition gives
\[
 s_{C(w)}\le M_1-g(1-p)-(r-s)^2(1-p-m)-s(s-w)(3-s_6).
\]

The [extended Fourier estimate](rank7_four_level_1231_packing.md)
gives \(\langle p s_6\rangle\le5+(59/32)\kappa\) for
\(\kappa\le11/200\), and the universal bound is six. The estimate
uses the shared-anchor defect \(\kappa=\langle p(1-p)\rangle\).
In the small-defect branch, the Fourier argument puts the two
leading spaces near distinct parallel rank-two stabilizer blocks,
with \(e_M+2e_x<6/25\). The paired-code syndrome contains total
six-mode wedge trace at most five, since the pair-block masses
are each at most four and sum to six. Comparing the actual
weights \(p\) with the syndrome indicator yields the stated
\(59\kappa/32\) error. For the two branches we can therefore use
\[
 \langle p s_6\rangle\le5+c\kappa,\qquad
 c=\begin{cases}2&\text{if }\kappa\le11/200,\\
                 200/11&\text{if }\kappa\ge11/200.\end{cases}
\]
Multiply the pointwise inequality by \(p\) and use
\(\langle p\rangle=2\), \(p+m\le1\). The exact mixed
polarization then yields
\[
 2\langle u,L_-(C(w))\rangle\ge
       G\kappa +sw\nu-B_*,\qquad G=g-cs(s-w).
\]
Here \(u=\mathcal B E_H\) as in the three-level proof and
\(2\|u\|^2=\kappa\), with the polarization inner product understood
as real Hilbert–Schmidt. The charge cancels the reference decrease
\(s(s-w)\) and retains the remaining error in the coefficient
of \(\kappa\). The separate anticommuting defect remains at least
\(2J(C(w),C(w))\ge g^2\kappa/2\).

For compression take the fixed \(A+B\) block. The lowest amplitude
in the block is \(\sqrt{rsw}\); the largest outside is at most
\(s\max(r,\sqrt{s})\). The trace of this block is \(3+\nu+x\),
with \(\nu+x\in[\nu,1-\nu]\). The
[spectral compression estimate](rank7_compression_slack_astra.md)
thus yields the following lower bound on the actual compression
defect after its purity coefficient 96:
\[
 48s^2(\sqrt{r w/s}-\max(r,\sqrt{s}))_+^2\,\nu .
\]

## The two scalar estimates

Work on the positive exterior-gain branch. Then \(H>0\),
\(\nu>0\), and \(a=B_* /(sw\nu)\) is in \([0,2)\) since
\(H<g\). The inequality \(g>16s^2\) on \(H>0\) is the
[three-level scalar estimate](rank7_three_level_124_packing_and_scalar.md).
The uniform shared-anchor geometry gives \(K=\kappa/\nu\ge1/16\).
Per unit \(\nu\), Cauchy–Schwarz and the anticommuting bound give
combined payment at least
\[
 12 (GK+sw(1-a))_+^2/K+g^2K/2 .
\]
The exterior charge is at most \(168sw(H-ga/2)\) per unit \(\nu\).

For \(\kappa\le11/200\), take \(c=2\).
Here \(G>16sw\). Hence the positive-part cutoff is inactive and
the mixed bound is nondecreasing in \(K\ge1/16\), since
\(G\ge sw|1-a|/K\). Use \(K=1/16\). Subtracting the exterior charge,
the derivative in \(a\) is
\(24sw[(7/2)g-G-16sw(1-a)]>0\).
After adding the compression estimate, it suffices to certify
\[
 \frac34(G+16sw)^2+\frac{g^2}{32}
      +48s^2(\sqrt{rw/s}-\max(r,\sqrt{s}))_+^2-168swH>0 .
\]
For \(s\le r^2\), set \(r=z^2\), \(h=s/[r(1-r)]\le1/2\),
and \(\sqrt{w/s}=z+(1-z)v\) or \(zv\), according to the sign
of the compression gap. Divide by \([r(1-r)]^2\).
For \(s\ge r^2\), \(H>0\) gives \(r<1/3\). Write
\(\sqrt r=(3/5)z\), \(y=\sqrt{s/r}=\sqrt r+(71/100-\sqrt r)u\),
and \(\sqrt{w/s}=y+(1-y)v\) or \(yv\). Divide by \(r^2\).
Both domains are covered by unit cubes using \(h=u/2\) in the
first case. Exact Bernstein conversion and subdivision check
strict positivity on these four cubes.

For \(\kappa\ge11/200\), take \(c=200/11\) and
\(K\ge 11/100\) by \(\nu\le1/2\). We omit compression.
The difference of payment and exterior charge is increasing in \(a\).
On the positive-part branch the absolute derivative of the
mixed term is at most \(24sw[g+sw/K]<48gsw\), while the
gain charge decreases at rate \(84gsw\).
At \(a=0\), the derivative in \(K\) is \(g^2/2\) if the cutoff is
active, and otherwise \(12G^2+g^2/2-12(sw/K)^2\).
To see nonnegativity, write \(v=w/s\). For \(v\ge6/25\),
\(G\ge100v s^2/11\), by \(g>16s^2\). For \(v\le6/25\),
\(g^2/24>(100v s^2/11)^2\). Both dominate the required term
\((sw/K)^2\) in their respective regions. The least payment is
therefore at \(K=11/100\).

At that endpoint let \(L=(11/100)g+s^2(3v-2)\ge-(6/25)s^2\).
Then \(L_+^2\ge L^2-(36/625)s^4\), and it suffices to certify
\[
 (1200/11)[L^2-(36/625)s^4]+(11/200)g^2-168swH>0.
\]
Divide by \([r(1-r)]^2\), set \(h=s/[r(1-r)]=u/2\), and
use the cube \(0\le r,u,v\le1\). This cube covers the entire
positive-gain spectral region. The same exact verifier checks
all five cubes, in \(7,3,5,2,34\) Bernstein boxes, respectively.

## Strictness and unrestricted cuts

For each fixed positive spectrum with \(H>0\), the verified
positive scalar margins in both branches give a fixed
\(\varepsilon>0\) such that actual total payment exceeds
the bound on gain by at least \(\varepsilon\nu\).
Since \(168E(w)\le168swH\nu\), this comparison permits retaining
a strictly positive fraction of the actual nonnegative payment.
For example if the actual payment is \(P\), then
\(P\ge168E(w)+\varepsilon\nu\) and \(P\ge0\) imply
\((1-\theta)P\ge168E(w)\) for
\(\theta=\varepsilon/(168swH+\varepsilon)\) on the gain branch.
When the exterior gain is nonpositive the entire payment can
be retained. This gives a uniform strict defect margin at every
fixed spectrum, including tie limits. The
[open-neighborhood transfer](rank7_open_interior_neighborhood.md)
gives the asserted neighborhoods. The two-sided Cauchy–Schwarz
reduction and stability under adding stabilizer auxiliary
qubits extend the single-unitary comparison to all cuts.

[Independent review and separate exact recomputation](reviews/rank7_four_level_1231_independent_review.md)
