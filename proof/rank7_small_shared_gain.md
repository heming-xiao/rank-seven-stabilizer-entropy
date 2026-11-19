# Rank-seven optimality when the shared-anchor gain is small

November 18, 2026. For every ordered positive rank-seven Schmidt
spectrum \((\alpha,\beta,\gamma,a,b,c,d)\) set
\[
 h=\alpha-\beta,\qquad k=\beta-\gamma,\qquad q=\gamma-a,\qquad
 L=h+2k+3q,\qquad g=hq.
\]
The sorted computational representative globally minimizes order-two
nonlocal stabilizer Rényi entropy on every qubit bipartition, over
all complex local unitaries, whenever
\[
                         5g\le bL.                                      \tag{1}
\]
The first or third gap may separately be arbitrarily large.
In particular \(h\le3b/5\) suffices regardless of the other six
weights, and \(q\le b/5\) recovers the older bounded middle-gap
criterion. The margin is at least \(1/101\) of the actual paired
defect. All optimizers are the local Clifford images of the sorted
representative up to global phase.
[Earlier middle-gap theorem](rank7_near_third_fourth.md) ·
[Rank-seven equality characterization](rank7_all_tie_equalities.md).

## Uniform absorption and compact comparison

Normalize \(d=1\). Keep the notation \(n,v,M,p,\rho,\Delta,R,A\)
and the two analytic outer bounds of the middle-gap proof.
The signed exterior bound there uses \(q\le b/5\) only when
absorbing the shared gain in a fifth of the weighted singleton loss.
On the larger domain (1) directly use
\[
                     cgn\le bcLM/5,\qquad n\le M.
\]
The constant term, highest-pair deficit, and nonnegative completion
coefficient are unchanged. The same mixed shift \(5\Delta/4\) leaves
payment minus exterior gain bounded below by \(AvB\), with
\[
 B=2+\frac{(4/5)bcL}{2}+\rho\Delta p^2-\rho\Delta+
              \frac{(45/4)\Delta^2+R}{(5/2)A}.
\]
The positive-spectrum tests \(L\ge13\) and \(a+b+c\ge4\) absorb the
remaining quadratic debit by the same completed-square bounds,
without restricting \(q/b\). The \(v=0\) case already has
nonnegative payment before compression.

For the compact part set
\[
 (h,k,q,p,b-c,c-1)
    =(13u_1,(13/2)u_2,(13/3)u_6,u_3,u_4/2,u_5/3).
\]
This time the \(q\) coordinate is independent of \(b\).
The outer conditions are certified at lower corners by
\(u_1+u_2+u_6\ge1\) or \(u_3+u_4+u_5\ge1\).
The separation test for the highest-pair cut is still
\(\beta c-\gamma ab\ge0\); on such boxes the same rational
compression payment suffices. On all other boxes the base
comparison or one of the two analytic bounds is sufficient.
The compact scalar inequality is verified over the complete
two-simplex product, without an additional restriction (1)
inside the polynomial checker. Condition (1) is needed for the
physical reduction to that inequality.

The exact tree has 441 base leaves, 165 compression leaves and
28 outer leaves, with maximum depth 24. This pays
\(A E=(101/100)168 E\) from the actual defects whenever the
exterior gain \(E>0\). Nonpositive gain retains the full defects.
The usual paired reduction and stabilizer padding give all cuts.
[Exact verifier](../verification/verify_rank7_small_shared_gain.py) ·
[Paired transfer and open neighborhoods](rank7_open_interior_neighborhood.md).

