# Full-spectrum leading-triangle polarization through the completion density

Let the ordered seven probabilities be \((\alpha,\beta,\gamma,a,b,c,d)\), with \(d>0\). In the [three-probe notation](rank7_triangle_probe_tail_equalization.md) put \(g=(\alpha-\beta)(\gamma-a)\), \(\Delta=(\beta-\gamma)(\alpha-a)\), \(j=(\beta-c)(\gamma-b)\), \(\rho_{45}=c(b-d)\), \(\rho_{46}=d(b-c)\), \(j_t=j-\rho_{45}\). Let \(P\) be the leading three-space, \(w=\mathcal B\Lambda^2P\) its triangle probe, \(p_1=p_{01}\), \(p=p_{01}+p_{02}\), \(r=p+p_{12}\), \(\eta=\langle r(1-r)\rangle\), \(\lambda_1=\langle p_1(1-r)\rangle\), \(\lambda=\langle p(1-r)\rangle\). Let \(U_\triangle\) be the weighted triangle occupancy minus its computational value. For each tail \(s\in\{3,4,5,6\}\) use \(A_s=w_{012s}\). The unweighted occupations \(A_4,A_5,A_6\) vanish in the computational frame.

Define the nonnegative spectral prices
\[
 B_4=[c(a-d)-\gamma(a-b)]_+,\quad
 B_5=[ab-cd-\gamma(a-c)]_+,\quad
 B_6=[ab-cd-\gamma(a-d)]_+ .
\]
For every spectrum, every physical frame, and arbitrary local qubit dimension,
\[
 \boxed{\quad
 2\langle w,L_-(C)\rangle\ge
 U_\triangle-3\sum_{s=4}^6 B_s A_s+\Delta\lambda_1+g\lambda+j_t\eta
 +\rho_{45}(1-\langle r p_{45}\rangle)
 +\rho_{46}(1-\langle r p_{46}\rangle).
 \quad} \tag{1}
\]
Every correction on the right has zero reference value. The final two terms are nonnegative. In the earlier tail cone \(\gamma(a-b)\ge c(a-d)\), all three \(B_s\) vanish. Below we also give an open region outside that cone where the completion penalties can be fully absorbed in an actual joint mixed payment. Formula (1) is a mixed-sector inequality, one input to the full computational-basis comparison.

## Three lower-block moments of the skew compression

For each skew label \(b'\) let \(r_{b'}\) be its leading triangle weight. When \(r_{b'}>0\), let \(n_{b'}\) be the kernel vector of the skew compression of \(J_{b'}\) to \(P\), and \(t_{b'}=J_{b'}n_{b'}\in P^\perp\). The block \(P^\perp J_{b'}P\) has one singular value one with left singular vector \(t_{b'}\). Its other two singular values are both \(\sqrt{1-r_{b'}}\), with their left singular vectors orthogonal to \(t_{b'}\). Thus the compression to \(P^\perp\) of the image-space projection is
\[
 P^\perp J_{b'}P J_{b'}^\dagger P^\perp
  =|t_{b'}\rangle\langle t_{b'}|+(1-r_{b'})\Pi_{b'},
\]
where \(\Pi_{b'}\) is a rank-two projection. At \(r_{b'}=1\) any orthogonal two-plane will do; at \(r_{b'}=0\) the label carries no weight in the identity below. By the [exact Pfaffian expression for the one-hole density](rank7_triangle_quantitative_rigidity.md),
\[
 \left\langle r_{b'} P^\perp J_{b'}P J_{b'}^\dagger P^\perp\right\rangle
 =3R_\omega+H,\qquad
 H=\langle r_{b'}(1-r_{b'})\Pi_{b'}\rangle,\quad
 0\preceq H\preceq\eta I,\quad \operatorname{Tr}H=2\eta . \tag{2}
\]
Here \(\omega\) is a unit leading volume, \(\langle x_s,R_\omega x_s\rangle=A_s\), and \(\langle\cdot\rangle\) is the skew-label sum normalized by \(D/2\). In particular, with \(d_s=\sum_{i=0}^2 p_{is}\),
\[
 \langle r d_s\rangle=3 A_s+\langle x_s,H x_s\rangle .
\]
The sum of the diagonal errors on any three specified tails is at most \(2\eta\), and each is at most \(\eta\).

## A reference-saturated conditional matching in four spectral chambers

Start with the complete seven-vertex graph weighted by \(t_i t_j\). Subtract \(\rho_{45},\rho_{46}\) on \(45,46\), so the three internal edges of \(4,5,6\) all cost \(cd\). Subtract \(B_s\) additionally on every edge from any of \(0,1,2\) to \(s=4,5,6\).

For a matching containing a leading edge \(i i'\), the best score is \(t_it_{i'}+za+cd\), with \(z\in\{\alpha,\beta,\gamma\}\) the remaining head. If \(z\) pairs with \(3\), this score is achievable. If it pairs with \(4\), the other edge costs at most \(ac\), giving the competing completion \(zb-B_4+ac\le za+cd\). Pairing with \(5,6\) instead gives competing completions at most \(zc-B_5+ab,\ zd-B_6+ab\), also at most \(za+cd\). Without \(z\) the best completion is at most \(ab+cd\le za+cd\). Partial matchings obey the same bound.

Without a leading edge the exact maximum after these subtractions is
\(\alpha a+\beta b+\gamma c-B_4-B_5\).
Indeed the three untruncated expressions defining \(B_4,B_5,B_6\) are consecutive in descending order, with successive differences \((\gamma-a)(b-c)\), \(\gamma(c-d)\). Taking positive parts preserves the order and only decreases these differences. Thus for every leading weight \(z\) the four scores \(za,zb-B_4,zc-B_5,zd-B_6\) are descending. The smallest is at least \(cd\), since \(ab\le\gamma a\) implies \(B_6\le d(\gamma-c)\). Any tail–tail edge can be replaced by an edge to a free head: use its endpoint \(3\) when present, otherwise the old price was only \(cd\). Missing edges can also be added with nonnegative price. Among matchings with all three heads matched to tails, choose the largest three tails and pair them in order; the subtracted tail prices are unchanged by permuting their head partners. This proves the maximum.

Relative to the old conditional maxima, the three leading types all decreased by \(\rho_{45}\), while the nonleading type decreased by \(B_4+B_5\). Thus their consecutive gaps are \(\Delta,g,j_t+B_4+B_5\). At a skew label, the edge vector has a probability representation by ordinary matchings, with the leading types having probabilities \(p_{01},p_{02},p_{12}\). Writing \(M_{02}=\alpha\gamma+\beta a+bc\), the original pointwise score obeys
\[
 s_C\le M_{02}-\rho_{45}+\Delta p_1-g(1-p)
 -(j_t+B_4+B_5)(1-r)
 +\rho_{45}p_{45}+\rho_{46}p_{46}+\sum_{s=4}^6 B_s d_s .
\]
Multiply by \(r\) and use the exact triangle polarization. In the Fano frame each of \(p_{45},p_{46}\) has all its mass inside the triangle's three direction classes; the last sum of added costs has zero \(r\)-weighted reference value. From (2) and \(B_4\ge B_5\ge B_6\ge0\),
\[
 \sum_{s=4}^6 B_s\langle x_s,Hx_s\rangle\le (B_4+B_5)\eta .
\]
This is precisely paid by the extra conditional gap, yielding (1). A [standard-library exact verifier](../verification/verify_rank7_full_spectrum_triangle_polarization.py) also checks each matching in each possible active prefix of the three \(B_s\). All 928 tests use the 28 quadratic coefficients in forward gaps; 901 are directly nonnegative and 27 require subtracting one defining chamber polynomial.

## A positive price for unused leading completion

Define \(x=1-\sum_{s=3}^6 A_s\ge0\). For all sorted spectra put
\[
                 l=\min\{a(\gamma-b),\ c(\gamma-d)\}.
\]
The right side of (1) can be increased by \(3l x\). Subtract this uniform price from every head–tail edge. In a type with a leading edge the optimal completion still uses one head–tail edge: without it the score is at most \(ab+cd\le za+cd-l\). The three leading optima thus decrease by \(l\), and the \(01\) type with a wholly tail completion requires \(l\le a(\gamma-b)\).

In the nonleading type the optimal scores before this uniform shift at cross-edge counts \(0,1,2,3\) are respectively
\[
 ab+cd,\quad\alpha a+cd,\quad\alpha a+v+cd,\quad\alpha a+v+w',
 \qquad v=\beta b-B_4,\quad w'=\gamma c-B_5 .
\]
At count one this is the earlier completion comparison with \(z=\alpha\). At count two, if \(a\) lies on a tail–tail edge \(a y\), exchange it with a tail \(t_s\) matched to a head \(z\). The possible loss is \(a y-cd-z(a-t_s)-B_s\le0\) by the definition of \(B_s\); thus \(a\) can be a head partner. If \(a\) was unused instead, exchanging it into a head edge also increases the score. Assigning the two heads to \(a,b\) then attains the stated optimum. Since \(v\ge w'\) and \(w'-cd=\min\{a(\gamma-b),c(\gamma-d)\}=l\), the count-three score after subtracting \(3l\) dominates the count-two and count-one scores after their respective shifts. It also dominates the count-zero score since \(a(\alpha-b)\ge l,\ v\ge l,\ w'-cd=l\). The count-two and count-three optima tie after this shift, so \(l\) is the largest uniform shift preserving the prescribed nonleading optimum.

The third gap in the conditional matching therefore increases by \(2l\). In the \(r\)-polarized comparison the reduced reference score supplies \(3l\), while the added-back uniform tax subtracts \(l\sum_{s=3}^6\langle r d_s\rangle\). Using (2), the net change is exactly
\[
 3l x + l\left(2\eta-\sum_{s=3}^6\langle x_s,Hx_s\rangle\right)
 \ \ge\ 3l x .
\]
This positive price can be used along with every subsequent bound and requires no anticommuting or compression reserve. The verifier checks 1,856 additional comparisons in the eight combined tax and shift chambers, totaling 51,968 quadratic coefficient checks. At the spectrum below \(l=49/5\), giving additional polarization price \(147x/5\).

## Two interfaces for the weighted exterior bounds

For strict tails the [six-row triangle packing identity](rank7_three_price_head_expansion.md) gives
\[
 -U_\triangle\ge \sum_{s=4}^6 (a-t_s)
          (\alpha+\beta+\gamma-b-c-d+t_s) A_s.
\]
This follows by retaining the corresponding terms in \(D_A\) and in the separate \(t_s(a-t_s)A_s\) loss, and dropping the other nonnegative terms. Let \(\theta\) be the largest ratio of \(3B_s\) to the coefficient of \(A_s\) here, omitting zero numerators. Then (1) remains true with its first two terms replaced by \((1+\theta)U_\triangle\). This gives a pure weighted-price formulation for every strictly ordered spectrum. On degenerate tails (1) itself always applies.

There is also a way to retain the original unit coefficient of \(U_\triangle\) on an open set beyond the previous tail cone. Suppose \(B_6=0\), \(\xi=3B_4\le\rho_{45}\) and \(\Delta\rho>0\), with \(\rho=\min\{b(c-d),(\gamma-c)(a-b)\}\). Put \(u_{45}=\mathcal B P_{45}\), \(2\|u_{45}\|^2=\kappa_{45}\). The disjoint-pair polarization and one physical complement-pair row imply
\[
 2\langle w,u_{45}\rangle=T_{45}-\langle r p_{45}\rangle,\qquad
 T_{45}=\sum_{e\subset\{0,1,2\},\,|e|=2}w_{e45}\le1-A_4-A_5 .
\]
Consequently \(1-\langle r p_{45}\rangle\ge A_4+A_5-\sqrt{\eta\kappa_{45}}\). Retain only \(\xi\) of this nonnegative reference price in (1). Since \(B_5\le B_4\), it pays the full completion penalty, leaving \(-\xi\sqrt{\eta\kappa_{45}}\).

In the mixed square shifted by \(s=G_+\) on the shared probe, \(t=\Delta\) on the highest-pair probe and \(z\ge0\) on the triangle, the highest-pair bound already supplies \(12\Delta\rho\,\kappa_{45}\). Completing the square against \(-24z\xi\sqrt{\eta\kappa_{45}}\) gives a total lower price \(-12z^2\xi^2\eta/(\Delta\rho)\) for these two terms. All three Gram cross coefficients are still nonnegative (\(s\le g\)), independently of the old cone. Thus the [previous joint mixed formula](rank7_triangle_probe_tail_equalization.md), equation (6), applies with its \(12\Delta\rho\,\kappa_{45}\) term spent and its coefficient of \(\eta\) replaced by
\[
 12z\left[2j_t-z\left(1+\frac{\xi^2}{\Delta\rho}\right)\right].\tag{3}
\]
The anticommuting and compression payments remain independently available. When \(j_t>0\), this price is nonnegative through \(z=2j_t/(1+\xi^2/(\Delta\rho))\).

For example take \((36,12,8,159/100,3/2,7/5,1)\). The compression ordering inequalities \(\gamma d>ab,\ \alpha cd>\beta ab\) hold strictly. The previous tail condition fails strictly. Here \(B_4=53/500\), the raw prices of \(B_5,B_6\) are strictly negative, \(\xi=159/500<\rho_{45}=7/10\), \(\Delta=3441/25\), \(\rho=297/500\), \(j_t=341/5\). At \(z=j_t\) the fraction \(\xi^2/(\Delta\rho)=2809/2271060<1/800\) of the former triangle \(\eta\) coefficient is spent. The inequalities have slack, so this full-price third-probe payment persists in an open neighborhood with more than \(799/800\) of the former \(\eta\) coefficient.
