# A sharp highest-pair loss on a fixed rank-seven frame

November 18, 2026. For ordered Schmidt probabilities
\((\alpha,\beta,\gamma,a,b,c,d)\), put \(h=\alpha-\beta\),
\(k=\beta-\gamma\), \(q=\gamma-a\), \(g=hq\), and
\(\Delta=k(h+k+q)\). Compare this spectrum to
\((\alpha-k,\gamma,\gamma,a,b,c,d)\) on the same physical frame.
Write \(E,E_0\) for the normalized four-exterior gains against
their respective computational references. With the highest-pair
weighted difference \(U_1\) as in [the split identity](rank7_leading_split_packing.md),
\[
 \boxed{E-E_0\le\Delta U_1-kq(q+3a-b-c-d)D_A\le\Delta U_1.}
 \tag{1}
\]
All three statements include \(k=0\) and vanishing spectral differences.

## Six pair capacities suffice for the \(q\)-dependent part

Use \(H=\{0,1,2\}\), \(R=\{3,4,5,6\}\), with tail values \(r_i=(a,b,c,d)_i\)
in that order. Write \(\delta X=X-X_*\) for a difference from the sorted frame.
For \(i,j\in R\), let \(A_i=w_{012i}\) and
\(T_{ij}=\sum_{\{u,v\}\subset H}w_{uvij}\) for \(i<j\).
The reference has \(A_3^*=1\), \(A_i^*=0\) for \(i>3\).
It has \(T_{ij}^*=1\) when \(i,j>3\) and zero otherwise. Thus
\[
 D_A=a-\sum_i r_iA_i\ge0,\qquad
 T_{ij}+A_i+A_j\le1=T_{ij}^*+A_i^*+A_j^*.
 \tag{2}
\]
The first inequality follows from the three-leg completion capacity
\(\sum_i A_i\le1\) and \(r_i\le a\). For the second, sum all four-wedges
avoiding the two labels \(R\setminus\{i,j\}\). This gives exactly the five
terms displayed in (2) and has capacity one by the complement-pair row.
All are unconditional physical rows. [Original packing constraints](reviews/rank7_ambient_independent_review.md)

Let \(V_0,V_1\) denote the weighted differences for wedges with exactly
one of the highest labels, stripping off that label's probability.
Set \(L(q)=2(a+q)U_1(q)+V_0(q)+V_1(q)\), where only the first of the
five tail probabilities \((a+q,a,b,c,d)\) varies. A subscript or
argument zero on \(U_1,L,V_i\) in this paragraph sets \(q=0\).
Then
\[
\begin{aligned}
 U_1(q)&=U_1(0)-qD_A,\\
 L(q)-qU_1(q)
 &=L(0)+q\left[\sum_{i<j}r_ir_j\,\delta T_{ij}-3aD_A\right]-q^2D_A.
\end{aligned}
\tag{3}
\]
Indeed \(U_1(0)=-aD_A+\sum_{i<j}r_ir_j\delta w_{01ij}\), while the
coefficient of \(q\) in \(V_0+V_1\) is
\(\sum_{i<j}r_ir_j\delta(w_{02ij}+w_{12ij})\).

The constant \(L(0)\le0\) follows coefficient by coefficient.
With the first two entries \(a+\lambda\), the third and fourth entries
both \(a\), the coefficient of \(\lambda\) in the full exterior gain is
\(L(0)\). Its forward quartic terms have exactly one gap with index \(1\)
and three indices in \(\{3,4,5,6\}\). All 20 are ordinary certified
coefficients. This uses the individual forward certificates and avoids
differentiating a one-sided bound. [Exact forward verification](rank7_forward_coefficients_independent.md)

Writing \(t=a+b+c+d\), (2) gives
\[
 \sum_{i<j}r_ir_j\,\delta T_{ij}
 \le-\sum_i r_i(t-r_i)\,\delta A_i
 =(t-a)D_A-\sum_i r_i(a-r_i)A_i
 \le(b+c+d)D_A.
 \tag{4}
\]
Combining (3) and (4) gives \(L(q)\le qU_1(q)-q(q+3a-b-c-d)D_A\).
Finally the exact simultaneous-raise identity is
\(E-E_0=k(h+k)U_1(q)+kL(q)\), which proves (1).

## Loss retained after the shared-pair correction

Let \(v_1=L_{01}-2\) and \(B_1=d^2v_1-U_1\). The five-tail prefix
packing proves \(B_1\ge qD_A\). The shared weighted difference changes
by \(-kD_A\), so paying its extra loss at price \(g/2\) consumes
at most \(kh B_1/2\). Formula (1) gives, on every frame,
\[
 E-E_0\le d^2\Delta v_1-(\Delta-kh/2)B_1-kgD_A/2.
 \tag{5}
\]
In particular the retained price \(\Delta-kh/2\) exceeds or equals
\(\Delta/2\) by \(k(k+q)/2\). The additional explicit \(D_A\) term
in (1) may be retained on its own or used first for the shared correction.
[Five-tail prefix and shared-probe identity](rank7_leading_split_packing.md)

## A physical equality case

Take the sorted computational frame and interchange labels 5 and 6,
with \(b>0\), \(c>d\), and \(k>0\). Then \(v_1=D_A=0\),
\(U_1=-b(c-d)\), and \(E_0=0\). Indeed the reference four-wedges
are \(0123,0145,0246,0356,1256,1346,2345\). Under this interchange
their net change in the weighted overlap is
\[
 b(c-d)(-\alpha\beta+\alpha\gamma+\beta a-\gamma a)
 =-k(\alpha-a)b(c-d)=\Delta U_1 .
\]
Thus \(\Delta\) is the largest possible universal coefficient on
\(B_1\) at price \(d^2\Delta v_1\), even for physical stabilizer frames.
The normalized quantities are homogeneous, so this example can be
scaled to a probability vector of sum one.

## A separate reduction of the highest-pair gain coefficient

The \(q\)-free constant in (3) admits the stronger upper bound
\(L(0)\le-bcd\,v_1\). Use the ordinary forward costs for fifteen
of the twenty coefficients in \(L(0)\). In the other five cubic
monomials, use the following slopes on \(v_1\) for reference cost
minus actual cost.

| Cubic forward indices after stripping index 1 | Slope |
|---|---:|
| 456 | 1 |
| 466 | 1 |
| 556 | 1 |
| 566 | 2 |
| 666 | 1 |

These slopes are the coefficients of
\((b_4+b_5+b_6)(b_5+b_6)b_6=bcd\) in the original forward gaps
\(b_i=t_i-t_{i+1}\), \(b_6=d\). Each of the five inequalities uses
only directed-link and complement-pair capacities. The
[standalone exact verifier](../verification/verify_rank7_highest_pair_split_loss.py)
stores the sparse prices, reconstructs all cubic costs for both
the six-pair proof and this refinement, and compares all 1,225
columns with rational arithmetic. Hence the following is a second
available comparison:
\[
 E-E_0\le\Delta U_1-kbcd\,v_1-kq(q+3a-b-c-d)D_A .
\]
It can be used together with (1), equivalently replacing \(v_1\)
in this last charge by \((v_1)_+\). The physical swap example has
\(v_1=0\) and saturates this strengthened comparison as well.


