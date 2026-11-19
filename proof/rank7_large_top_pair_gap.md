# 高权重二重峰下的秩 7 全局最优性

2026-11-17。对任何量子比特二分割，若七个非零 Schmidt 概率的前两个相等，且其余各项都至多为该共同概率的 \(1/32\)，则排序计算基代表在任意复局部酉下全局最优。后五项可任意不等。该证明直接使用主目标的非负缺陷，绕开待证的普适五点上界。

全篇共同缩放概率，令 \(t_0=t_1=1\)，并令 \(r=t_2\le1/32\)。写 \(C=N^2=P_X+K\)，其中 \(P_X\) 是首二本征方向的秩二投影，\(K\) 是其正交补上五个正概率组成的算子，且 \(0\preceq K\preceq rI\)。记 \(Y\) 为 \(K\) 的五维支撑，\(q=4/d\)。

## 1. 只需支付一个固定二平面的超额

沿用 [一般物理维数归约](rank7_ambient_reduction.md) 的 \(x_B\) 和逆谱差 \(b_h=a_h-a_{h-1}\)（\(a_i=1/t_i,b_0=a_0\)）。因为 \(b_1=0\)，既有 75 项无条件三次系数证书中，九个未覆盖单项式只剩 \(222,223,224,233\) 四种。

设 \(H=\{2,3,4,5,6\}\)。这四种系数只用 \(B\subset H\)，把三元组改记为互补边 \(H\setminus B\)。总边权 \(V\) 即固定 \(X\) 和五维 \(Y\) 的物理五点量。有向计数不再需要：每顶点度至多 1，因为对应权重的三元组都包含在四点集 \(H\setminus\{v\}\) 中。四个系数分别为

$$
 V,\quad 2V+\deg(2),\quad V+\deg(2)+\deg(3),\quad V+2\deg(2).
$$

计算基参考中 \(V=2,\deg(2)=\deg(3)=1\)。因此 \(c_\mathrm F(C)-c_\mathrm F(M^2)\le q W(V-2)_+\)，其中

$$
\begin{aligned}
W&=(\prod_i t_i)b_2\big[(b_2+b_3)^2+b_2b_4\big]\\
 &=t_5t_6\left[(1-t_2)(1-t_3)^2\frac{t_4}{t_3}
                +(1-t_2)^2\frac{t_3-t_4}{t_2}\right]
 \le t_5t_6\le r^2.
\end{aligned}
$$

最后一界利用 \(0<t_4\le t_3\le t_2\le1\)，括号两项分别至多 \(t_4/t_3\) 和 \(1-t_4/t_3\)。因此由 [Sierant 的 Proposition 2、Theorem 7](https://arxiv.org/html/2609.13106v2) 和计算基处取等，

$$
G_\mu(U)-G_\mu(I)
\le 168r^2(V-2)_+-\mathcal D(N),\qquad
\mathcal D(N)\ge \Delta_d(C)/d .
$$

## 2. 固定二平面靠近秩二稳定子码时，超额为平方量

在完整二外积空间中定义 \(M_Y\) 的二次型为

$$
\langle\alpha,M_Y\alpha\rangle
=q^{-1}\sum_{i<j\le5}\|\Pi_\mathrm F(\alpha\wedge y_i\wedge y_j)\|^2,
$$

其中 \(y_i\) 为 \(Y\) 的标准正交基。允许非物理的任意二形式 \(\alpha\)，也不要求此处 \(\alpha\perp Y\) 的支撑。对固定 \(i\)，以 \(j\) 的满标架补全和应用原文 Theorem 17 得上界 \(\|\alpha\wedge y_i\|^2\le\|\alpha\|^2\)。双计数 \(i,j\) 得 \(0\preceq M_Y\preceq(5/2)I\)。记 \(L=2I-M_Y\)，故 \(-I/2\preceq L\preceq2I\)，\(\|L\|\le2\)。

对于任何稳定子单位向量 \(e\)，\(L\) 在 \(e\wedge E\) 上的压缩非负。其理由是 [稳定子锚点界](reviews/rank7_two_link_independent_review.md) 给固定含 \(e\) 的二平面及与它正交的任意五维空间的 \(2\) 上界。对于原 \(Y\) 未与二平面正交的情形，只把 \(P_Y\) 压缩至二平面的正交补。它是介于零和其支撑投影之间的正收缩，秩至多五。取二外积保持该序，且双收缩输出都在正交补上，故仍有上界。若支撑不足五维，可扩到五维。

设 \(R\) 是一个秩二稳定子码投影，以其中标准正交稳定子基 \(e_0,e_1\) 张成 \(\alpha_0=e_0\wedge e_1\)。记 \(\sigma=\|P_X-R\|_{\rm HS}^2\)、\(e=\sigma/2\)。将 \(X\) 的单位二楔 \(\alpha\) 正交分解为

$$
\alpha=t\alpha_0+\eta_0+\eta_1+\zeta,
\quad
\eta_j\in e_j\wedge R^\perp,\quad
\zeta\in\Lambda^2 R^\perp.
$$

主角公式给 \(\|\eta_0+\eta_1\|^2\le e\)、\(\|\zeta\|\le e/2\)，无需把主角基自身当作稳定子基。取 \(d_0=\langle\alpha_0,L\alpha_0\rangle\ge0\)。两条稳定子星形压缩的 Cauchy–Schwarz 给

$$
|\langle\alpha_0,L\eta_j\rangle|\le
\sqrt{d_0}\,\sqrt{2}\|\eta_j\|.
$$

把两项与 \(|t|^2d_0\) 完成平方，损失至多 \(4\|\eta_0+\eta_1\|^2\)。用 \(L\succeq-I/2\) 控制 \(\eta\) 本身及 \(\zeta\) 本身，用 \(\|L\|\le2\) 控制含 \(\zeta\) 的交叉项，得总损失至多

$$
\frac92 e+2 e+\frac{e^2}{8}\le7e\qquad(0\le e\le2).
$$

因此对每个 \(R\) 都有 \(V-2\le(7/2)\sigma\)。

## 3. Pauli 缺陷支付该超额

令 \(\mathcal F_{\rm P}(A)=\sum_W\operatorname{Tr}(WA)^4\)（无重复符号的 Hermitian Pauli 基），且

$$
\delta=8-\mathcal F_{\rm P}(P_X)/d\ge0.
$$

最后的非负性来自 \(|\operatorname{Tr}(W P_X)|\le2\) 及 Pauli Parseval。

### 3.1 近端：\(\delta\le3/4\)

所有满足 \(|\operatorname{Tr}(W P_X)|>\sqrt2\) 的 Pauli 两两对易。事实上对归一态 \(P_X/2\)，反对易的两个 Hermitian Pauli 的期望平方和至多 1。把这些标签延拓为极大对易组，并在共同稳定子基中对 \(P_X\) 去相干。对没有被此组保留的系数 \(c_W\)，有 \((4-c_W^2)c_W^2\ge2c_W^2\)，故非对角 Hilbert–Schmidt 范数平方至多 \(\delta/2\)。

取上述去相干矩阵对角值最大的两个坐标的秩二投影 \(R\)。对角值 \(\lambda_i\in[0,1]\) 且总和为 2。因此 \(\sum_i\lambda_i^2\le\lambda_1+\lambda_2\)，因为在同一容量区域上权为 \(\lambda_i\) 的线性目标由其前两项取 1 最大化。故

$$
\sigma=4-2(\lambda_1+\lambda_2)
\le2(2-\sum_i\lambda_i^2)\le\delta.
$$

令 \(S_R\) 为原对易组中在两个坐标上作用符号相同的子群，大小 \(d/2\)。对每个 \(s\in S_R\)，因 \(W_s\) 在 \(R\) 上为标量 \(\pm1\)，

$$
|\operatorname{Tr}(W_s C)|\ge 2-\sigma-5r>1.
$$

对任何不在 \(S_R\) 中央化子的 Pauli \(a\)，\(S_R\) 恰有一半（\(d/4\) 个标签）与它反对易。Theorem 14 的无序反对易项于是给

$$
\frac{\Delta_d(C)}d
\ge\frac{4}{d^2}
\sum_{\{a,b\}\text{ 反对易}}\operatorname{Tr}(W_aC)^2\operatorname{Tr}(W_bC)^2
\ge\|C-\mathcal E_{S_R}(C)\|_{\rm HS}^2,
$$

其中 \(\mathcal E_{S_R}\) 是按 \(S_R\) 联合特征空间去相干。它的一个对角块是 \(R\)，故最后范数平方至少是 \(\|[C,R]\|_{\rm HS}^2\)。在 \(C\) 的本征基上，高二特征空间与其余空间间的间隙至少 \(1-r\)，给 \(\|[C,R]\|^2\ge(1-r)^2\|[P_X,R]\|^2\)。若主角的正弦平方为 \(s_1,s_2\)，则 \(\|[P_X,R]\|^2=2\sum_j s_j(1-s_j)\ge(1-\sigma/2)\sigma\ge(5/8)\sigma\)。

综合得到 \(\Delta_d(C)/d\ge(5/8)(1-r)^2\sigma\)。它支付要求的 \(168r^2(V-2)_+\)，因为该量至多 \(588r^2\sigma\)，且
\((5/8)(31/32)^2-588/32^2=101/8192>0\)。

### 3.2 远端：\(\delta\ge3/4\)

记 \(p_W=\operatorname{Tr}(WP_X)\)、\(k_W=\operatorname{Tr}(WK)\) 及 \(u=\operatorname{Tr}(K^2)\le5r^2\)。因 \(P_XK=0\)，归一化 Parseval 给 \(\sum_W p_Wk_W/d=0\)。故 \(\mathcal F_{\rm P}(C)/d\) 的一次交叉项可用 \(p_W^3-4p_W\)，而
\(\sum_W (p_W^3-4p_W)^2/d\le4\delta\)。因此该项至多 \(8\sqrt5\,r\sqrt\delta\)。

利用 \(|p_W|\le2\)、\(|k_W|\le5r\) 及 \(\sum_W k_W^2/d=u\)，余下二次、三次、四次项依次至多 \(24u,200r^3,125r^4\)。谱项 \(3[\operatorname{Tr}(C^2)]^2-2\operatorname{Tr}(C^4)\ge8+12u\)，且 \(c_\mathrm F(C)\ge0\)。所以

$$
\frac{\Delta_d(C)}d
\ge \delta-8\sqrt5\,r\sqrt\delta-60r^2-200r^3-125r^4.
$$

对 \(r\le1/32,\ \delta\ge3/4\)，令 \(v=\sqrt\delta\)。前两项至少为 \(v^2-(9/16)v\)，在 \(v\ge\sqrt{3/4}\) 递增，且用 \(\sqrt{3/4}\le7/8\) 得其下界 \(33/128\)。扣掉三个余项后的精确有理数 \(202371/1048576\) 大于 \(84/1024\)。由整体 \(M_Y\preceq(5/2)I\)，待支付的超额至多 \(84r^2\le84/1024\)。因此远端也成立。

## 4. 结论

第 3 节支付第 1 节的全部可能超额，证明平衡问题的主目标。由原文单酉归约适用两个任意复局部酉。对不平衡大小，在小侧补纯计算基辅助比特并外延原局部酉即可，原计算基值同样不变。

这里的 \(1/32\) 是便于手算核验的充分常数，不主张锐利。证明覆盖了以往几条谱锥都不能覆盖的极强二重峰，包括任意不等的五个弱概率；一般秩 7 仍开放。
