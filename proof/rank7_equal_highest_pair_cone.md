# A rank-seven spectral region with two equal highest probabilities

November 17, 2026. For Schmidt probabilities proportional to
\((1,1,r,t,a,b,s)\), with \(1\ge r\ge t\ge a\ge b\ge s>0\), assume
\[
 r+t+a\le 1+b.
\]
Then the descending computational-basis representative globally minimizes
order-two nonlocal stabilizer Rényi entropy on every qubit bipartition.
Every such spectrum has a full relative open neighborhood of optimality in
the rank-seven probability simplex. The five lower probabilities can be
distinct, and the neighborhood allows the two leading probabilities to split.

## Weighted overlap

Write \(p=(r,t,a,b,s)\), let \(w_{ij}\) be the normalized occupancy of
the wedge containing both highest labels and the tail pair \(i,j\), and
write \(w^*\) for the two edges \((1,2),(3,4)\) in the computational
representative. Define
\[
 \nu=\sum_{i<j}(w_{ij}-w^*_{ij}),\quad
 U=\sum_{i<j}p_i p_j(w_{ij}-w^*_{ij}),\quad
 \gamma=1-r-t-a-b+s .
\]
Denote the normalized linear exterior-overlap gain by
\(E=(c_F-c_{F,\mathrm{CB}})/q\). The
[forward coefficients](rank7_forward_coefficients_independent.md) give
\(E\le s^2(1-r)(1-t)\nu\).
The [weighted packing and matching estimate](rank7_tied_head_positive_branch.md)
gives
\[
 E\le\sum_{i<j}p_i p_j[\gamma+(p_i-s)+(p_j-s)](../literature/w_{ij}-w^*_{ij})
 \le\gamma U.
\]
For \(\gamma\ge0\), the same proof controls \(U>0\) by the sum of a
mixed-sector defect and an exterior compression defect with a positive
coefficient margin. The bound \(E\le\gamma U\) covers \(U\le0\).
It therefore suffices to work with \(\gamma<0\) and \(\nu>0\).

## The fourth prefix controls its extension to the fifth

For \(1\le h,k\le5\), write \(S_{hk}\) for the sum of directed
weights \(w_{ij}\) for \(i\le h,j\le k,i\ne j\) and let
\(\Delta_{hk}=S^*_{hk}-S_{hk}=\Delta_{kh}\). The one-hole degree bound
and the three-point edge bound give \(\Delta_{hk}\ge0\) except at
\((5,5)\), where \(\Delta_{55}=-2\nu\).
Indeed for \(h<k\) the reference achieves directed weight \(h\);
for \(h=k\le4\) it achieves \(2\lfloor h/2\rfloor\).

Set \(d_h=p_h-p_{h+1}\) for \(h<5\), \(d_5=s\), and
\(\lambda_h=p_h+p_{h+1}-s\) for \(h<5\), \(\lambda_5=0\).
The forward differences of \(p_i(p_i-s)\) are \(d_h\lambda_h\).
Expanding the weighted packing bound in nested prefixes gives
\[
 E\le \gamma s^2\nu-
 \frac12\!!\sum_{(h,k)\ne(5,5)}
 d_h d_k(\gamma+\lambda_h+\lambda_k)\Delta_{hk}.
\]
The spectral hypothesis is precisely \(\gamma+2b\ge s\). Since
\(\lambda_h\ge b\) for \(h<5\), the terms with both indices below
five are individually nonnegative. For each \(h=1,2,3\), the two
reference sums \(S^*_{h4}\) and \(S^*_{h5}\) coincide, so
\(\Delta_{h4}\ge\Delta_{h5}\). Combining the two off-diagonal terms
\((h,4)\) and \((h,5)\) after symmetry, their total is at least
\[
 d_h[ (\gamma+\lambda_h+b)(b-s)+(\gamma+\lambda_h)s]
 \Delta_{h5}
 = d_h b(\gamma+\lambda_h+b-s)\Delta_{h5}\ge0.
\]
For \(h=4\), write \(I=\sum_{i<j\le4}w_{ij}\) and
\(J=\sum_{i\le4}w_{i5}\). Then
\(\Delta_{44}=4-2I\), \(\Delta_{45}=4-2I-J\), and
\(\Delta_{44}-2\Delta_{45}=2(I+J-2)=2\nu>0\).
The half-weight diagonal term \((4,4)\) together with \((4,5)\)
therefore gives the same bound with \(h=4\).
This accounts for every term involving index five, leaving a nonnegative
sum. Thus \(E\le\gamma s^2\nu<0\).

Whenever \(E\le0\), the purity comparison retains the full normalized
defect. The positive-payment case retains a fixed positive fraction of
the defect at each spectrum, since the certified scalar inequality is
strict. The [strict-margin transfer](rank7_open_interior_neighborhood.md)
gives the open-neighborhood statement. The two-sided comparison follows
by the paired Cauchy–Schwarz reduction and stabilizer padding.

For general tied leading probabilities, the method leaves
\(r+t+a>1+b\) with \(\gamma<0\), \(U<0\), and \(\nu>0\) to be
controlled outside the previously established classes.

[Sierant, Lemma 1 and Proposition 2](https://arxiv.org/html/2609.13106v2) · [Edmonds, matching polytope theorem](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn1-2p125_A1b.pdf)
