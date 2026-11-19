# Rank-seven three-level spectra with two highest probabilities

November 17, 2026. Normalize the highest probability to one. For every \(k=1,2,3,4\) and \(1\ge r\ge s>0\), the spectrum consisting of two ones, \(k\) copies of \(r\), and \(5-k\) copies of \(s\) has sorted computational-basis optimality at order two, over arbitrary local unitaries on every qubit bipartition. No size restriction on the gaps is needed. In addition every such spectrum has a relative open neighborhood of exact optimality, so its level equalities can be split.

## Weighted matching and projected mixed defect

Take the two leading lines \(X\), and denote the five tail probabilities by \(t_i\), \(i\in T=\{2,\ldots,6\}\). Write \(w_{ij}\) for the normalized four-wedge occupancy of the two leading lines together with tail labels \(i,j\). Let
\[
 V=\sum_{\{i,j\}\subset T}w_{ij},\qquad
 W=\sum_{\{i,j\}\subset T}t_it_j w_{ij},\qquad
 U=W-W_{\rm CB},\qquad W_{\rm CB}=t_2t_3+t_4t_5.
\]
Here \(V\le7/3\). In the skew Pauli basis of the two-exterior, let \(u\) be the odd projection of the leading rank-one two-wedge projector, and let \(L_-\) be the odd projection of \(\Lambda^2 C\) as in the [mixed defect identity](rank7_two_level_defect_transport.md). With \(p\) the normalized diagonal weight of the leading wedge and \(\langle p\rangle=1\), put \(\kappa=\langle p(1-p)\rangle=2\|u\|^2\). The [skew Pauli rounding bound](rank7_wedge_pauli_rounding.md) gives \((V-2)_+\le4\kappa\).

For each Pauli the seven-by-seven skew compression has entries with squared moduli \(p_{ij}\) on unordered pairs. Its row sums are at most one, and every odd subset of size \(m\) has total weight at most \((m-1)/2\), since a skew contraction has even rank. Thus these values form a convex combination of matchings by the matching-polytope theorem. Write \(p=p_{01}\) and \(s_C=\sum_{i<j}t_it_j p_{ij}\). Conditional on the matching containing edge \(01\), its maximal weight is \(1+t_2t_3+t_4t_5\). Conditional on excluding it, the maximal weight is \(t_2+t_3+t_4t_5\): use both leading lines with the two largest tails and match the two next largest tails. In the latter case an unused leading line can replace a tail endpoint on a tail-tail edge, and exchanging any leading partner for a larger tail never decreases the sum, because the leading probability is the largest. The remaining tail pairs maximize adjacent products in sorted order, by the two-pair rearrangement identity. Thus
\[
 s_C\le 1+W_{\rm CB}-(1-p)\mu,\qquad
 \mu=(1-t_2)(1-t_3).
\]
The exact mixed polarization gives \(2\langle u,L_-\rangle=1+W-\langle p s_C\rangle\), hence
\[
 2\langle u,L_-\rangle\ge U+\mu\kappa .
\]
When \(U>0\), Cauchy–Schwarz gives
\[
 \|L_-\|^2\ge (U+\mu\kappa)^2/(2\kappa).
\]
In all below cases \(U\le a(V-2)\) with \(a=s^2\) or \(a=rs\), and so \(\kappa\ge U/(4a)\). If \(\mu\ge4a\), the displayed lower bound is increasing for \(\kappa\ge U/(4a)\). Consequently the actual defect, which is at least \(24\|L_-\|^2\), pays at least \(3(\mu+4a)^2U/a\). Without that comparison the arithmetic–geometric mean gives at least \(48\mu U\).

The high-block compression slack, after its purity coefficient, pays at least \(64d_0(V-2)\ge64d_0U/a\), where
\[
 d_0=(\sqrt{t_5t_6}-\sqrt{t_2t_3t_4})_+^2.
\]
Indeed the amplitudes of wedges containing both leading labels are at least \(\sqrt{t_5t_6}\), and all others are at most \(\sqrt{t_2t_3t_4}\). The high-block trace rounding in the [compression-slack proof](rank7_compression_slack_astra.md) then gives this bound.

## A weighted packing inequality used in all four cases

For each tail pair \(e\), use its complement-index pair capacity and multiply by the product of the other three tail probabilities. The sorted arrangement saturates every such row. Summing bounds the increment of all one-head contributions by
\[
 -\sum_{f\subset T,\ |f|=2}
    \left(\prod_{i\in f}t_i\right)\left(\sum_{i\in T\setminus f}t_i\right)
                   (w_f-w_f^{\rm CB}).
\]
Indeed a both-head wedge with tail pair \(f\) enters three rows, indexed by pairs in \(T\setminus f\); a one-head wedge enters the unique row indexed by its two complementary tail labels. The all-tail contributions cannot exceed the sorted value, since the high-high complement row bounds their total occupancy by one and the sorted all-tail plane \(2345\) carries the largest tail four-product. Including the both-head difference \(U\) gives, for \(E=(c_{\rm F}(C)-c_{\rm F}(C_{\rm CB}))/q\),
\[
 E\le (1-3r)U+(r-s)F,\qquad
 F=\sum_{\substack{f\subset T\\|f|=2}}
    |(T\setminus f)\cap T_s|\left(\prod_{i\in f}t_i\right)
    (w_f-w_f^{\rm CB}),
\]
where \(T_s\) denotes the labels assigned value \(s\). Write \(A,B,C'\) for the summed occupancies of \(ss,rs,rr\) tail pairs, respectively, allowing empty types. For each fixed tail label, the one-hole row bounds its incident occupancy by one; for any triple of tail labels the five-plane row bounds the occupancy of its three edges by one.

## The four multiplicities

For \(k=3\) the sorted masses are \((A,B,C')=(0,1,1)\). The mid-level degree sum gives \(B+2C'\le3\), and \(C'\le1\) by the triple row. Hence \(a=s^2\) gives \(U\le a(V-2)\), and \(F=rs(B-1)+2r^2(C'-1)\le0\). Thus \(E\le(1-3r)U\). For \(k=4\), the sorted masses are \((0,0,2)\), \(C'\le2\) by the four mid-level degree rows, and \(F=r^2(C'-2)\le0\). Here \(a=rs\) gives \(U\le a(V-2)\), and the same gain bound holds. In these two cases \(r\ge1/3\) gives \(t_0\le3t_4\), so the [unbounded-spread cone](rank7_unbounded_spread.md) applies even for arbitrarily small \(s\). For \(r\le1/3\), \(U\le0\) gives the exterior comparison immediately. When \(U>0\), \(\mu=(1-r)^2\ge4a\). The compression gap \(d_0\) is \((s-r^{3/2})_+^2\) at \(k=3\), and \((\sqrt{rs}-r^{3/2})_+^2\) at \(k=4\). Both cases reduce to
\[
 3[(1-r)^2+4r^2 x^2]^2+64r^2(x-\sqrt r)_+^2
                      -168(1-3r)r^2x^2>0
\]
with \(x=s/r\) or \(x=\sqrt{s/r}\), respectively. For \(x\ge\sqrt r\) this is the common Bernstein certificate below. For \(x\le\sqrt r\), the compressed term is zero; after division by \(r^2x^2\) the mixed payment decreases with \(x\) since \(r x\le(1-r)/2\). Thus the verified endpoint \(x=\sqrt r\) suffices.

For \(k=2\), the sorted masses are \((1,0,1)\). Put \(\alpha=1-C'\ge0\), \(\beta=1-A\ge0\); the mid-level degree sum gives \(B\le2\alpha\). Then \(U=-r^2\alpha+rsB-s^2\beta\le s^2(V-2)\). Also
\(F=-3r^2\alpha+2rsB-s^2\beta\le U\), so \(E\le(1-2r-s)U\). To handle \(U\le0\) at any \(r\), use the forward expansion in \(b_1,b_3,b_6\): every possible exceptional monomial has \(b_1\)-degree two. All degree-two terms in \(b_1\) force both leading labels and give difference \(b_1^2 U\), so \(E\le b_1^2 U\). For \(U>0\), \(B\le2\alpha\) forces \(s>r/2\). Thus \(r\ge2/5\) gives \(E\le0\). On \(9/25\le r<2/5\), the unrestricted mixed payment \(48(1-r)^2\) exceeds \(168(1-2r-s)\) since the latter is at most \(16.8\) and the former at least \(17.28\). For \(r\le9/25\) with positive gain, \((1-r)^2\ge4s^2\): use \(s\le r\) for \(r\le1/3\) or \(s<1-2r\) otherwise. Since \(s>r/2\), the gap \(s-r\sqrt{s}\) is positive. Writing \(z=\sqrt r,\ y=\sqrt{s/r}\), the remaining condition is
\[
 3[(1-r)^2+4s^2]^2+64r^2 y^2(y-z)^2-168(1-2r-s)s^2>0 ,
\]
the second polynomial certificate below.

For \(k=1\), the sorted masses are \((1,1,0)\) and \(B\le1\) by the unique mid-level degree. Thus \(U\le s^2(V-2)\), and
\[
 E\le(1-r-2s)U+(r-s)rs(B-1).
\]
If \(s\ge1/3\), the prior ratio cone applies. If \(V\le2\), both exceptional forward terms give no excess, because \(\gamma_{02}=0\). Otherwise \(A-1>0\). When \(1-r-2s\le0\), rewriting the displayed bound as
\(s^2(A-1)(1-r-2s)+rs(B-1)(1-3s)\)
makes both terms nonpositive. If \(1-r-2s>0\), only \(U>0\) remains. Here \(\mu=(1-r)(1-s)\ge4s^2\) using \(s<1/3\) and \(1-r>2s\). The high-block gap is \(s(1-\sqrt r)\). With \(d=1-r\), \(x=2s/d\) and \(z=\sqrt r\), dividing the payment-minus-gain comparison by \(d^2\) gives
\[
 3[1+d(x^2-x/2)]^2+16x^2(1-z)^2-42dx^2(1-x)>0.
\]
This is the third certificate below.

## Exact certificates and open extension

The [rational verifier](../verification/verify_rank7_three_levels.py) checks all three positive polynomials by tensor Bernstein conversion and bisection. For the first use \(z=\sqrt r\in[0,3/5]\) and \(x=z+(1-z)u\), \(u\in[0,1]\). The second uses \(z\in[0,3/5]\), \(y\in[7/10,1]\), and the third uses \(z,x\in[0,1]\). The three certified minima are respectively \(1458591/512000000\), \(8296961913236337/2569011200000000000\), and \(41463/16777216\). These are exact rational coefficient bounds. Positive comparison is strict in each paid regime; the direct nonpositive exterior regimes already leave the full defect. Thus for each fixed three-level spectrum a positive fraction of its actual paired defect remains after paying any gain. The [open-neighborhood transfer](rank7_open_interior_neighborhood.md) then applies with half the smallest reference probability. Paired Cauchy–Schwarz and stabilizer padding give the stated result on every bipartition.

[Original two-sided reduction and Pauli constraints](https://arxiv.org/html/2609.13106v2) · [Edmonds, matching polytope theorem](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn1-2p125_A1b.pdf)
