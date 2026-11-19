# An exact residual price for transferring unequal leading probabilities

November 18, 2026. For an ordered rank-seven spectrum
\((\alpha,\beta,\gamma,a,b,c,d)\) use
\(h=\alpha-\beta\), \(k=\beta-\gamma\), \(q=\gamma-a\), \(p=a-b\),
\(X=h+k+q\), \(\Delta=kX\), \(g=hq\), and
\(R=k^2(k^2+(h^2+q^2)/2)\). Set
\[
 T=p(a-c)+(b-d)(c-d),\quad D_0=d^2-T,\quad K=5/2,\quad
 \sigma=(\sqrt{\alpha\beta cd}-\sqrt{\alpha\gamma ab})_+.
\]
On every qubit bipartition, the sorted computational representative
is globally optimal for every ordered spectrum satisfying
\[
\begin{aligned}
 \frac{12(2t\Delta-t^2)+R}{K}
   +\max(g^2/24,q^4/72)+64\sigma^2
  \ \ge\ & (168\Delta-24t)D_0-168kbcd\\
 &-168pkq\left[
    (1-24t/(168\Delta))X+q+3a-b-c-d-h/2
                          \right] ,                                  \tag{1}
\end{aligned}
\]
for one \(0\le t\le2\Delta\).
At \(\Delta=0\), use the exact tied-middle theorem.
The optimal \(t\) for (1) is the projection of
\(\Delta+K(D_0-pq)\) onto \([0,2\Delta]\).
Unlike the previous comparison the positive residual is priced
by the actual tail discount \(D_0\), and the completion loss
remains available after the simultaneous shared comparison.
[Previous unweighted residual](rank7_leading_split_joint_payment.md).

## Transport on the same frame

Use \(E\) for the normalized exterior gain on the actual spectrum
and \(E_0\) for the gain after lowering the first two weights by
\(k\), leaving \(h,q\) fixed. Let \(D_A\) be the completion deficit,
with \(D_A\ge p v_+\) for the highest-pair excess \(v=L_{01}-2\).
The same-frame split gives
\[
 E\le E_0+\Delta U_1-kbcd\,v_+
             -kq(q+3a-b-c-d)D_A.
\]
At the lowered spectrum \(U_0\) is the weighted shared-pair
difference, and \(U=U_0-kD_A\) is its actual value. Therefore
\(O=E_0-kgD_A/2\) can be bounded by the exact tied-middle
shared comparison on the actual frame. On \(\nu\le0\) use
\(O\le0\). On \(\nu>0\) use
\[
 O\le cdH\nu-\tfrac g2 B,\qquad
 B=cd\nu-U,\qquad H=g-b(h+3q)-5b^2/2 .
\]
This is the same domain and actual shared probe for which the
previous proof pays \(168O\) with the mixed square and one half
of the three leading anticommuting slots.
[Full tied-middle theorem](rank7_equal_middle.md) ·
[Tail transfer and split identity](rank7_harmonic_tail_transport.md) ·
[Shared comparison with half the slots](rank7_leading_split_joint_payment.md).

The highest-pair prefix comparison yields
\(U_1\le D_0 v_+-qD_A\) including \(v\le0\), where the signed discount multiplies zero.
Since \(168\Delta-24t\ge0\), subtract its mixed charge from the
remaining gain, and put \(\rho_t=1-24t/(168\Delta)\). We obtain
\[
\begin{split}
 168(E-O)-24tU_1\le{}&
 \big[(168\Delta-24t)D_0-168kbcd\big]v_+\\
 &-168kq\big[\rho_t X+q+3a-b-c-d-h/2\big]D_A.
\end{split}
\]
The bracket is nonnegative: \(\rho_t\ge5/7\), \(X\ge h\),
and \(3a\ge b+c+d\). Substituting \(D_A\ge p v_+\) gives
exactly the right side of (1) times \(v_+\).

## Actual physical payments

In the same mixed norm use the shared shift from the tied-middle
comparison and the highest shift \(t\). Its Gram cross coefficient
\(s\Delta+tg-st\) is nonnegative for \(0\le s\le2g\) and
\(0\le t\le2\Delta\), by checking the endpoints in \(t\).
The older shared proof can use \(s<2g\) when its bound is positive
and \(s=0\) otherwise. Consequently the remaining highest
mixed and anticommuting slots pay
\([12(2t\Delta-t^2)+R]v_+/K\). The unused half of the
shared anticommuting slots pays
\(\max(g^2/24,q^4/72)v_+\) by the two existing physical bounds.
The independent highest-pair compression pays
\(64\sigma^2 v_+\). These are distinct payments, so (1) suffices.
Only the terms \( -12(t-\Delta)^2/K+24t(D_0-pq)\) depend on
the shift after moving the right side to the left, giving the
claimed optimizer. A strictly positive residual margin in (1)
and the existing strict shared comparison also give a positive
per-spectrum paired margin and hence local Clifford equality.
[Physical slot and compression bounds](rank7_leading_split_joint_payment.md).

## A strict example outside the previous main comparisons

Take \(d=1,\ h=15,\ k=1/4,\ q=6,\ p=1/1000,\ b=191/100,\ c=189/100\).
All seven probabilities are distinct. There is no highest-pair
separation, so (1) uses no compression payment. The condition in
the previous unweighted residual fails, even with its optimal
highest shift. The harmonic-tail comparison and the small
shared-gain criterion both fail. The discount \(D_0\) and the
completion term in (1) give a strictly positive exact margin.
[Exact example checker](../verification/verify_rank7_weighted_split_residual.py).

