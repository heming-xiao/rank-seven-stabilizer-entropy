# Transporting the tied-middle theorem with a five-tail prefix loss

November 18, 2026. Let the positive sorted rank-seven Schmidt probabilities
be proportional to \((\alpha,\beta,\gamma,a,b,c,d)\). The sorted
computational representative minimizes order-two nonlocal stabilizer
Rényi entropy on every qubit cut and over arbitrary complex local
unitaries whenever
\[
 \boxed{\quad d\le \frac{bc}{b+c}.\quad} \tag{1}
\]
In particular \(c\ge2d\) suffices without any constraint on the first five
probabilities. There is a second region above the harmonic threshold.
Write \(p=a-b,\ q=\gamma-a,\ h=\alpha-\beta,\ k=\beta-\gamma,\
X=h+k+q,\ g=hq,\ \Delta=kX\) and define
\[
                         T=p(a-c)+(b-d)(c-d).
\]
A sufficient condition, including (1), is
\[
                          T+pq/2\ge d^2 . \tag{2}
\]
A still stronger condition depending on the head gaps is
\[
 \boxed{\quad X(d^2-T)\le bcd+
                    p q[h/2+k+2q+3a-b-c-d].\quad} \tag{3}
\]
Every fixed spectrum covered by these comparisons has a positive
defect margin and a relative open rank-seven neighborhood. The
margin fraction used below may depend on that spectrum. The
[rank-seven equality theorem](rank7_all_tie_equalities.md) identifies
the optimizers as the local Clifford images of the sorted reference,
up to the common overall phase.

## A simultaneous weighted loss on the highest pair

Use the 35 normalized four-wedge occupancies on one physical frame.
Put \(v=L_{01}-2,\ \nu=L_{01}+L_{02}-4,\ e=1-w_{0123}\) and
\(x=1-\sum_{j=3}^6w_{012j}\). For the auxiliary spectrum with first
four entries equal to \(a\), write \(U_1^0\) for the weighted difference
of pair \(01\) from its sorted value. Its five possible completion
labels \(2,3,4,5,6\) have weights \((a,a,b,c,d)\).
The two selected reference edges are \(23,45\).
In this section edge \(ij\) has physical mass \(w_{01ij}\).
Let \(I_4\) be the internal edge mass on the first four
completion labels \(2,3,4,5\). Then
\[
 d^2v-U_1^0\ \ge\
       p(a-c)e+(b-d)(c-d)(2-I_4),\qquad
 2-I_4\ge\max(0,v,\nu/2),\quad e\ge\max(0,v,\nu). \tag{4}
\]
Both simultaneous prices apply on a single frame. In particular
\(U_1^0\le d^2v-Tv_+\).

For the proof let \(P_{ij}\) be the directed edge sum with first
endpoint in the initial \(i\) completion labels and second in the
initial \(j\) labels, and let \(\delta_{ij}=P_{ij}^*-P_{ij}\).
All these deficits are nonnegative except at \((5,5)\), which
supplies \(-2v\). This is the [five-tail prefix bound](rank7_equal_highest_pair_cone.md).
The weighted edge sum is its symmetric bilinear expansion with
half weight, using gaps \(p,b-c,c-d,d\) at prefix lengths \(2,3,4,5\).
In this expansion \(\delta_{22}/2=e\) and
\(\delta_{44}/2=2-I_4\). If \(I_3\) denotes the edge mass on
\(2,3,4\), then \(P_{23}=w_{0123}+I_3\) and
\(P_{34}=I_4+I_3\). The three-point constraint gives \(I_3\le1\).
Thus \(\delta_{23}\ge e\) and \(\delta_{34}\ge2-I_4\).
Those four disjoint prefix terms give exactly (4), since
\(p^2+p(b-c)=p(a-c)\) and \((b-c)(c-d)+(c-d)^2=(b-d)(c-d)\).

The first four completion degrees sum to \(L_{01}+I_4\le4\).
Together with \(I_4\le2\) this proves \(2-I_4\ge v_+\).
The stronger shared bound \(I_4+(L_{01}+L_{02})/2\le4\)
uses the directed row with complement containing 6 and missing 0,
the complement four-set row on \(1345\), and the four one-hole
degree rows omitting one of \(2,3,4,5\). Each price is \(1/2\)
except the row on \(3456\), which takes price one. The
[top-four price](rank7_low_head_tail_prices.md) gives the other
bound on \(e\). The [exact verifier](../verification/verify_rank7_harmonic_tail_transport.py)
checks every column, the four prefix reference values and the
shared row prices using rational arithmetic.

## A fixed-frame lift preserving the shared-probe loss

Compare the actual frame to the same frame at probabilities
\((\alpha-k,\gamma,\gamma,a,b,c,d)\), retaining \(h,q\). Write
\(E,E_0\) for the normalized exterior gains and \(U,U_0\) for
the weighted shared-probe gains. Let
\(D_A=a-\sum_{j=3}^6t_jw_{012j}\ge bx+pe\).
The exact probe identities give
\(U=U_0-kD_A,\ U_1=U_1^0-qD_A\).
The [fixed-frame split inequality](rank7_highest_pair_split_loss.md)
and (4) give
\[
 \begin{split}
 E-E_0&\le\Delta U_1-kbcd\,v_+
             -kq(q+3a-b-c-d)D_A\\
 &\le(\Delta(d^2-T)-kbcd)v_+
        -q[\Delta+k(q+3a-b-c-d)]D_A . \tag{5}
 \end{split}
\]
The surplus \(D_A\) coefficient after reserving \(kgD_A/2\) is
\[
 q[\Delta+k(q+3a-b-c-d)]-kg/2
        =kq[h/2+k+2q+3a-b-c-d]\ge0 .
\]
Since \(D_A\ge p v_+\), (3) implies
\[
                          E\le E_0-\tfrac12kgD_A . \tag{6}
\]
The statement includes \(k=0\) directly. Condition (2) suffices
for (3) because the square bracket on its right is at least \(X/2\).
Finally (1) is equivalent to \((b-d)(c-d)\ge d^2\).
Under (1) there is also a direct view of (6): (4) gives
\(U_1^0\le0\), so the first line of (5) is at most
\(-\Delta qD_A\le-kg D_A\).

## Transfer of both physical defect regimes

Set \(S=cd,\ H=g-b(h+3q)-(5/2)b^2\).
If \(\nu\le0\), the forward bound gives \(E_0\le Sg\nu\le0\);
then (6) suffices. If \(\nu>0\), the [full tied-middle theorem](rank7_equal_middle.md)
gives \(B_0=S\nu-U_0\ge0\) and
\(E_0\le SH\nu-gB_0/2\).
Combining with (6) yields on the actual spectrum
\[
 B=S\nu-U=B_0+kD_A\ge0,\qquad E\le S H\nu-gB/2 . \tag{7}
\]
Thus on \(E>0\) we have \(H>0,\ g>16b^2\) and
\(0\le z=B/(S\nu)<2\), exactly the domain of the tied-middle
scalar comparison. This also proves a pure exterior subregion:
throughout (3), \(H\le0\) implies \(E\le0\) on every frame.

For the actual general spectrum its shared mixed polarization has
the same lower coefficient \(G=g-\lambda(b^2-S)\), and the extra
term \(\Delta c_1\) is nonnegative. Here \(\lambda=2\) for
\(\kappa\le11/200\), or \(200/11\) otherwise. The disjoint
anticommuting pay \(2J(C,C)\ge g^2\kappa\) also persists. Hence,
with \(K=\kappa/\nu\), the actual mixed and anti payment per unit
\(\nu\) is at least
\[
                12[GK+S(1-z)]_+^2/K+g^2K .
\]
The small-defect estimate uses \(K\ge1/12\), and the large-defect
estimate uses \(K\ge11/100\). Both bounds depend only on the
frame. Because \(h,q,b,S,H\) have been held fixed and (7) supplies
the actual value of \(z\), the certified scalar comparisons in the
tied-middle theorem apply unchanged to \(168E/\nu\). No comparison
of the full physical defects at two different spectra is required.
[General matching inequality](rank7_general_two_probe_matching.md) ·
[Anticommuting and shared estimates](rank7_shared_anchor_twelve_and_anticommuting.md)

At a fixed positive spectrum the two scalar comparisons leave
a positive amount proportional to \(\nu\), while \(E\le SH\nu\).
This retains a positive fraction of the actual defects on \(E>0\).
On \(E\le0\) they are all available. The paired reduction and
stabilizer padding give the unrestricted two-sided result on every
cut, and strict transfer gives the claimed neighborhood.
[Paired comparison and open neighborhoods](rank7_open_interior_neighborhood.md)

For a strict point above the harmonic threshold take
\[
              (72,\ 8,\ 6,\ 21/8,\ 5/2,\ 3/2,\ 1).
\]
Here \(b(c-d)=5/4<cd=3/2\),
\((a-b)(\gamma-b)=7/16<cd\), and the old one-percent condition
also fails. Nevertheless \(T=57/64<1\) and
\(T+pq/2=141/128>1\), with \(H>0\).
More generally at these same five smallest probabilities,
(2) proves every \(\beta\ge6,\alpha\ge\beta\). The strict
inequalities persist upon small changes of all tail parameters,
giving a full-dimensional unbounded family inside the strip
\(1.01<c/d<2,\ b(c-d)<cd\).

