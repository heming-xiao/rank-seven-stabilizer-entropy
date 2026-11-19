# 秩七 1+2+4 谱的精确重叠区域

2026-11-17。令 Schmidt 概率为 \((1,r,r,s,s,s,s)\)，其中 \(0<s\le r\le1\)。在下列显式条件内，排序计算基在任意量子比特二分割上全局最优：

\[
r(1-r)-\left(2-\tfrac r2\right)s+\tfrac12 s^2\le0.
\]

例如 \(r=1/2\) 时，条件等价于 \(s\ge (7-\sqrt{41})/4\)，该端点约为 \(0.149\)。证明在正向外积系数中同时保留三个已有容量的负差。[正向系数](rank7_forward_coefficients_independent.md)

令 \(w_A=\|\Pi_F u_A\|^2/q\)，并写 \(T=\sum_A w_A\)、\(T_i=\sum_{A\ni i}w_A\)、\(L_{ij}=\sum_{A\supset\{i,j\}}w_A\)。排序参考值分别是 \(7,4,2\)。设 \(\nu=L_{01}+L_{02}-4\)。在该谱型中，正向差只有 \(b_0=1-r,b_2=r-s,b_6=s\) 可能非零，唯一需五点项的单项式为 \(b_0b_2b_6^2\)，该系数差恰是 \(\nu\)。故当 \(\nu\le0\) 时已有重叠比较。

## 三条同时成立的容量缺口

固定任一对 \(i,j\)，在补三元组的旧对容量中记 \(\delta_{HL}\) 为十个连接这两标签与其余五标签的对缺口总和。含恰好一个或两个 \(i,j\) 的补三元组都各贡献两个这类对，而总补三元组权为 \(T\)，不含这两个标签的总权为 \(L_{ij}\)。于是

\[
\delta_{HL}=10-2(T-L_{ij}),\qquad
L_{ij}-2=-(7-T)+\delta_{HL}/2.
\]

所有 21 个对的总缺口恰为 \(21-3T\)，故 \(L_{ij}-2\le(7-T)/2\)。对 `(0,1)` 与 `(0,2)` 分别使用该界，得到 \(T\le7-\nu\)。

旧有向容量给 \(T_i-L_{ij}\le2\)，而 \(\sum_{j\ne i} L_{ij}=3T_i\)。对 \(i=0\)，分离两条涉及第二层标签的固定对，得到

\[
3T_0\ge4+\nu+4(T_0-2),\qquad T_0\le4-\nu.
\]

对 \(i=1,2\) 各只分离其与 0 的固定对，得到 \(4-T_i\ge(L_{0i}-2)/2\)。因此 \(T_0+T_1+T_2\le12-3\nu/2\)。这些都是同一物理本征架上的约束，无需选择不同的第二层基。[旧容量的物理证明](reviews/rank7_ambient_independent_review.md)

## 保留负差后谱区间

不丢弃已证非正的三个项 \(b_6^4\)、\(b_0b_6^3\)、\(b_2b_6^3\)，其系数差分别是 \(T-7\)、\(T_0-4\)、\(T_0+T_1+T_2-12\)。它们和唯一有可能超过参考的系数不重叠。故当 \(\nu>0\)，

\[
\begin{aligned}
q^{-1}(c_F-c_{F,\rm CB})
&\le s^2 \left[(1-r)(r-s)-s^2-s(1-r)-\tfrac32 s(r-s)\right]\nu\\
&=s^2\left[r(1-r)-\left(2-\tfrac r2\right)s+\tfrac12 s^2\right]\nu.
\end{aligned}
\]

因此所列条件使重叠差非正。代入 Theorem 7、Proposition 2，得到单酉纯度比较，再由 Lemma 1 的双侧 Cauchy–Schwarz 和稳定子填充推广到任意切割。该证明仍留下上述二次系数为正的区间；在此区间用秩二双头混合投影直接输运会遇到一个秩二而非秩一的高二楔块 \(P_{x_0\wedge\operatorname{span}(x_1,x_2)}\)，目前的可分解单位二楔舍入不能直接为它提供所需稳定性。[双头混合证明](rank7_two_level_defect_transport.md) · [Sierant，Lemma 1、Proposition 2、Theorem 7](https://arxiv.org/html/2609.13106v2)

## 高二楔块零缺口的几何刚性

令 \(x=x_0\)、\(M=\operatorname{span}(x_1,x_2)\)、\(E_H=P_{x\wedge M}\)，\(m=d/2\)。在反对称 Pauli 框架中，记 \(J_a=W_a\mathrm{conj}\)、\(p_a=m(E_H)_{aa}=\|P_M J_a x\|^2\)。斜酉性给 \(p_a\in[0,1]\)，而 \(E_H\) 的迹为二，所以 \(m^{-1}\sum_a p_a=2\)。令 \(\kappa=m^{-1}\sum_a p_a(1-p_a)\)。通用混合极化给 \(\kappa=2\|\mathcal B E_H\|_{\rm HS}^2\)，因为 \(x\wedge M\) 内任意两个二楔的楔积均为零。[通用极化](rank7_two_level_defect_transport.md)

若 \(\kappa=0\)，所有 \(p_a\) 均为零或一，且有 \(d\) 个标签组成的集合 \(A=\{a:p_a=1\}\)。对 \(a\in A\)，\(J_a x\in M\)。这些向量张成 \(M\)，因为反对称 Pauli 正交基经收缩后有紧框架恒等式 \(m^{-1}\sum_a |J_a x\rangle\langle J_a x|=I-P_x\)。对两边压缩到 \(M\)，\(A\) 之外都没有贡献。

固定 \(a_0\in A\)，取 \(b\in A\) 使 \(J_b x\) 与 \(J_{a_0}x\) 线性无关。令 \(N=J_{a_0}^{-1}M\)，则 \(N=\operatorname{span}(x,W_{a_0+b}x)\)。写 \(w=a_0+b\)，则 \(W_w\) 保持 \(N\)。只要某 Pauli \(W_v\) 满足 \(W_vx\in N\)，便有 \(W_vW_wx=\pm W_wW_v x\in N\)，因此 \(W_v\) 保持整个 \(N\)。特别地，所有标签 \(a_0+a\)、\(a\in A\)，都属于保持 \(N\) 的 Pauli 标签群 \(H\)，故 \(|H|\ge d\)。

\(H\) 的辛秩至多二，因为在二维 \(N\) 上一对反对易 Pauli 的共同交换子只有标量，无法再容纳一对与前一对逐个对易的反对易算子。若辛秩为零，则 \(H\) 是最大对易群。此时 \(N\) 是同一稳定子本征基中两根不同线的和，两字符差的核正好定义一个二维编码。若辛秩为二，则 \(H\) 的辛中心至少有 \(n-2\) 个独立生成元。其限制均与反对易对交换，因而在 \(N\) 上为标量，所以 \(N\) 包含于同一中心字符的维数至多四的码块。

在两种情况中，\(N\) 所属的一个稳定子块与其 \(J_{a_0}\) 像由相同的生成元定义，只可能改变字符符号。Clifford 化后它们是两个相同方向的四点或更小仿射陪集，其并集含于一个八点仿射空间。于是 \(\operatorname{span}(x,M)\subseteq N+J_{a_0}N\) 同样在一个八点仿射空间。分别对二平面 \(\operatorname{span}(x,x_1)\) 和 \(\operatorname{span}(x,x_2)\) 应用固定二平面的仿射八点支撑界。每个平面的其余五根腿可以在整个物理空间内任意取向，因此这里得到 \(L_{01}\le2\) 和 \(L_{02}\le2\)，进而 \(\nu\le0\)。后续定量结论给 \(\nu_+\le59513\kappa\)，并把零缺口支撑收紧到仿射四点空间。[固定二平面仿射八点界](rank7_two_link_astra.md) · [共享首腿定量证明](rank7_shared_anchor_quantitative.md)
