# 五形式联合 Gram 界与固定测试形式的二平面判据

2026-11-17。下面把一般联合 Gram 界等价地写成一个二形式上的 Hermitian 型在 Grassmannian 上的非负性。给出一个精确的物理矩阵元，使这个型在完整线性空间上的半正定加强失败。该例还可逐项算出 Plücker 关系如何弥补负特征值。一般算子界仍待证。

## 任意五形式可先固定

取 $E=\mathbb C^d$、$q=4/d$。对任意五形式 $\Omega\in\Lambda^5E$，在 $\Lambda^2 E$ 上定义唯一的非负 Hermitian 算子 $M_\Omega$，其二次型为

$$
 \langle\alpha,M_\Omega\alpha\rangle
    =q^{-1}\sum_L\|a_{a_\alpha\psi_L}\Omega\|^2 .
$$

这里 $a_\zeta$ 为左楔乘 $\zeta$ 的厄米伴随。括号内连续两次以外积参数取伴随，最终关于 $\alpha$ 的振幅是线性的。$\psi_L$ 是按平面方向标记的正交基。

**等价条件。** 以下两条在每个固定物理维数等价。

1. 对每个正交单位对 $x,y$，归一化双收缩二体算子在 $\Lambda^5\big((\mathbb C x+\mathbb C y)^\perp\big)$ 上满足 $A_5\preceq2I$。
2. 对每个 $\Omega\in\Lambda^5 E$，算子 $2\|\Omega\|^2I-M_\Omega$ 在每个可分解二形式 $\alpha=x\wedge y$ 上具有非负期望。此处 $x,y$ 与 $\Omega$ 之间没有正交要求。

为证这点，对单位可分解 $\alpha$ 选取其支撑 $X$ 的标准正交基使 $\alpha=x\wedge y$。所有 $\beta_L=q^{-1/2}a_ya_x\psi_L$ 均在 $\Lambda^2R$，其中 $R=X^\perp$。$\Lambda^5E$ 按占据 $X$ 的粒子数 $j=0,1,2$ 正交分解为 $\Lambda^jX\wedge\Lambda^{5-j}R$。算子 $\sum_La_{\beta_L}^\dagger a_{\beta_L}$ 在各块等于 $I\otimes A_{5-j}$。

已知 $A_3\preceq I$（Sierant Theorem 20 的限制）。还自动有 $A_4\preceq2I$。事实上，在 $\Lambda^kR$ 上

$$
 \sum_i a_i^\dagger A_{k-1}a_i=(k-2)A_k .
$$

由于二阶湮灭与单阶湮灭交换，左边在每个 $\beta_L$ 项中给出 $a_{\beta_L}^\dagger(\sum_i a_i^\dagger a_i)a_{\beta_L}$，中间的数算子在残余 $k-2$ 粒子扇区取值 $k-2$。取 $k=4$ 及 $\sum_i a_i^\dagger a_i=4I$ 即可。故第一条给出所有块的上界 $2I$，得到第二条，齐次性覆盖一般范数。反向只需把测试五形式取在 $\Lambda^5R$。第一条与原先的联合 Gram 界等价。[三阶 CAR 归约](rank7_general_car_route.md)

对任一稳定子单位向量 $s$，已证的含稳定子态算子界结合上述占据分块，给出 $2\|\Omega\|^2I-M_\Omega$ 在整个线性空间 $s\wedge E$ 上的压缩为半正定。在任一稳定子基内，这控制所有共享顶点的边之间的二阶主子式。顶点互异的两条边可以有另一种表现。

## 精确负特征值与缺少的 Plücker 约束

取 $d=16$。前八坐标记作 $A$，后八坐标记作 $B$。置

$$
 a_i=e_{2i}\wedge e_{2i+1},\qquad
 b_i=e_{8+2i}\wedge e_{9+2i}\quad (i=0,1,2,3),\qquad
 \Omega=\frac{e_8\wedge(b_1\wedge b_2+b_1\wedge b_3+b_2\wedge b_3)}{\sqrt3}.
$$

取 $\alpha$ 支撑在 $A$，使它与 $\Omega$ 的支撑正交。原方向基为 $\psi_L=\sqrt q\sum_{F\parallel L}e_F$。色内方向的平面完全在 $A$ 或 $B$，在 $\alpha$ 和 $\Omega$ 的两次收缩后都无贡献。每个跨色方向有唯一非零色内差 $w$，以及色内商空间 $\mathbb F_2^3/\langle w\rangle$ 上的平移 $t$。一个差为 $w$ 的 $A$ 中坐标边收缩该方向，所得 $B$ 中二形式恰是经 $t$ 平移的同差坐标边。两条边都按升序，两个 $A$ 标签在两个 $B$ 标签之前，符号恒正。其他差的 $A$ 中坐标边则收缩为零。

特别在 $w=1$ 时，$a_i$ 得到 $b_{i\oplus t}$。收缩 $b_0$ 消去 $\Omega$。对 $j=1,2,3$，用 $a_{b_j}$ 收缩得 $e_8\wedge\sum_{\ell\in\{1,2,3\}\setminus\{j\}}b_\ell/\sqrt3$。这些向量的平方范数为 $2/3$，彼此的内积为 $1/3$。对四个 $t$ 求和，因此在四个 $a_i$ 上

$$
 (M_\Omega)_{ii}=2,\qquad (M_\Omega)_{ij}=2/3\quad(i\ne j).
$$

每个坐标二平面均使期望取二，而它们的归一化和 $\alpha_*=(a_0+a_1+a_2+a_3)/2$ 取到四。于是在此压缩上，$2I-M_\Omega$ 的四个特征值为 $-2,2/3,2/3,2/3$。$\alpha_*$ 的斜秩为八，超出可分解输入。

可以进一步只看前四坐标的**完整** $\Lambda^2\mathbb C^4$。把坐标边按 $01,23,02,13,03,12$ 排列，矩阵为

$$
 M_\Omega\big|_{\Lambda^2\mathbb C^4}\quad\text{的压缩矩阵}
 =
 \begin{pmatrix}2&2/3\\2/3&2\end{pmatrix}\oplus(4/3)I_4.
$$

核算后四项时，差为 $2$ 的后块边是 $8\,10$、$9\,11$、$12\,14$、$13\,15$。相应双占据概率为 $2/3,0,1/3,1/3$。差为 $3$ 的后块边是 $8\,11$、$9\,10$、$12\,15$、$13\,14$，仍是相同四个概率。对同一差的前块两条边，商平移把后块对应的两条边互换低位。它们的残余三形式正交或为零，故非对角项为零。不同 $w$ 的前块边从未出现在同一方向的 Gram 项。

另按十六个标签直接枚举所有 XOR 为零的四点坐标平面，以方向分组，依次精确收缩前块二边和五形式的三个坐标项。整数组合后除以 $3$，逐项复得上述两个有理矩阵。

对任意 $\alpha=\sum_{0\le i<j\le3} p_{ij}e_i\wedge e_j$，缺陷精确为

$$
 \langle\alpha,(2I-M_\Omega)\alpha\rangle
 =\frac23\left(
 |p_{02}|^2+|p_{13}|^2+|p_{03}|^2+|p_{12}|^2
 -2\operatorname{Re}(\overline{p_{01}}p_{23})
 \right).
$$

若 $\alpha$ 可分解，则 $p_{01}p_{23}=p_{02}p_{13}-p_{03}p_{12}$。取模及两次 $2ab\le a^2+b^2$ 正好给出非负性，复数系数也适用。这说明即使物理饱和值已在两个坐标二平面上达到，它们之间仍可保有严格正的相干矩阵元。把坐标端点的零缺陷用作普通 Gram 矩阵的零对角，或先将可分解输入线性化后申请半正定证书，都会丢失这项约束。

**一般缺口。** 对各个 $\Omega$，需证明 $2\|\Omega\|^2I-M_\Omega$ 在所有满足 $p_{ij}p_{k\ell}-p_{ik}p_{j\ell}+p_{i\ell}p_{jk}=0$ 的 $p$ 上非负。上面的精确矩阵示范了一个四坐标块的补偿方式。一般 $\Omega$ 使多个这样的块共享坐标边，尚未给出可同时支配其交叉项的系数分配。此处的负特征方向没有推翻物理 $A_5$ 或五维子空间不等式。
