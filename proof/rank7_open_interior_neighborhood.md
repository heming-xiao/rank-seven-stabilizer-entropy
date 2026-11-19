# Open interior rank-seven neighborhoods from a strict paired margin

November 17, 2026. A dimension-independent strict margin at one reference spectrum can be extended to a neighborhood of completely unrestricted spectra. Concretely there is a full open rank-seven neighborhood of
\[
 \bar t=\left(1,(199/200)^2,\tfrac14,\tfrac14,\tfrac14,\tfrac14,\tfrac14\right)
\]
in which the sorted computational state is optimal at order two over all local unitaries and every qubit bipartition. The neighborhood contains fully distinct probability spectra. In particular all seven probabilities can be bounded below by \(1/8\).

## Strict margin at the reference

Use the exact mixed-sector transport and compression slack inequalities in the [two-high comparison](rank7_two_level_defect_transport.md). For probabilities proportional to \((a,b,r,r,r,r,r)\), with \(a\ge b>r\), \(r\le a/3\), and \(v=L_{01}-2>0\), the overlap gain in purity is at most \(168 b(a-3r)r^2v\). The combined amount available from compression slack and actual defects is at least
\[
 \bigl[64a(\sqrt b-\sqrt r)^2+48(a-r)(b-r)\bigr]r^2v.
\]
At \(\bar t\), the first coefficient is exactly \(41.58105\) and the second exactly \(42.3225\). Thus the gain is covered by \(99/100\) of this amount. Since both the compression slack and the actual defects are nonnegative and the latter dominate \(\eta=\Delta_d(C)/d\), the full difference at the reference is
\[
 G_{\bar t}(V)-G_{\bar t}(I)\le-\eta_{\bar t}(V)/100 .
 \tag{1}
\]
For \(v\le0\) the overlap gain is nonpositive and the actual defect gives (1) directly.

## A uniform transfer argument

In a common frame let \(C_t,C_u\) have ordered eigenvalues \(t_i,u_i\in[s,1]\) on the same seven eigenvectors, and set \(\varepsilon=\max_i|t_i-u_i|\). The normalized defects satisfy
\[
 |\eta_t-\eta_u|\le5376\varepsilon .
 \tag{2}
\]
Indeed, in \(\eta_t=3(\tr C_t^2)^2-2\tr C_t^4+6d c_{\rm F}(C_t)-d^{-1}\sum_W c_W^4\), the first two terms have Lipschitz sum at most \(644\). The exterior term is a sum of 35 monomials of degree four with weights bounded by \(q=4/d\), giving \(3360\). For the Pauli term, each \(|c_W|,|c'_W|\le7\), giving \(|c_W^4-(c'_W)^4|\le98|c_W-c'_W|(|c_W|+|c'_W|)\). Pauli Parseval in the \(d^{-1}\)-normalized sum bounds the corresponding factor by \(\sqrt7\varepsilon\cdot2\sqrt7\), hence \(1372\varepsilon\).

Similarly,
\[
 \left|[G_t(V)-G_t(I)]-[G_u(V)-G_u(I)]\right|
 \le 19208\varepsilon/\sqrt s .
 \tag{3}
\]
For the paired pure vectors \(\psi_t=\sum_i\sqrt{t_i}|x_i,\bar x_i\rangle\), each norm is at most \(\sqrt7\), and their vector distance is at most \(\sqrt7\varepsilon/(2\sqrt s)\). Their unnormalized density matrices differ in Hilbert–Schmidt norm by at most \(7\varepsilon/\sqrt s\). Apply the same fourth-power inequality to their Pauli expectations, now with the physical dimension \(d^2\) in Parseval. The sum of the two individual Parseval norms is at most 14. This gives \(9604\varepsilon/\sqrt s\) for one frame and twice that for the subtracted comparison.

For the reference above take \(s=1/8\). Write \(\delta(s)>0\) for the [uniform low-defect cutoff](rank7_low_defect_interior.md), and choose the radius
\[
 \varepsilon_0=\min\{1/8,\ \delta(s)/(2\cdot5376),\
                     \delta(s)\sqrt s/(400\cdot19208)\}.
\]
If a new spectrum \(t\) is within this radius while normalized and ordered, then all its entries stay at least \(s\). For a frame with \(\eta_t\le\delta(s)\) the low-defect theorem suffices. Otherwise (2) gives \(\eta_{\bar t}\ge\delta(s)/2\), so (1) gives reference margin at least \(\delta(s)/200\); (3) spends at most \(\delta(s)/400\). Thus every frame obeys the new comparison and the two-frame Cauchy–Schwarz reduction and stabilizer padding give all physical cuts.

The same argument works whenever a verified reference spectrum has a strict defect-weighted margin like (1) and all seven probabilities are positive. It proves an unrestricted spectral neighborhood rather than requiring tails of exactly equal value. [Paired purity and defect source](https://arxiv.org/html/2609.13106v2)
