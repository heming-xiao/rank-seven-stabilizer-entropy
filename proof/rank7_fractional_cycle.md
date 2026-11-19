# 秩 7 组合放松的五环反例与物理泄漏下界

日期 2026-11-17。沿用 `rank7_fano_dual.py` 的标签 $V=\{0,\ldots,6\}$。设 $x_B=p_{V\setminus B}/q$，$B$ 取三元组，$q=4/d$，$p_A=\lVert\Pi_Fu_A\rVert^2$。本节先将 $x_B$ 当作组合放松里的独立变量。

## 精确见证

设 $R=\{2,3,4,5,6\}$。给三元组 $B$ 赋权如下，其余权重为零。

| 三元组 $B$ | 补边 $R\setminus B$ | $x_B$ | $b_2^2 b_3$ 的系数 |
|---|---|---:|---:|
| 234 | 56 | 1/2 | 2 |
| 236 | 45 | 1/2 | 2 |
| 256 | 34 | 1/2 | 2 |
| 345 | 26 | 1/2 | 3 |
| 456 | 23 | 1/2 | 3 |

补边构成五环 $2-3-4-5-6-2$。每对 $e\subset R$ 的覆盖和为 $R\setminus e$ 所诱导的边权和，至多两条环边，故至多 1。含 0 或 1 的对覆盖为零。每个四元组 $S\subset R$ 内的三元组权重和为缺失顶点的边度，恰为 1。若 $S$ 含 0 或 1，至多含一个带权三元组。每个顶点最多出现在三个带权三元组中，所以任意有序 $(v,u)$ 的 $\sum_{B:v\in B,u\notin B}x_B$ 至多 $3/2$。

在 $\prod_{i\in B}(\sum_{h\le i}b_h)$ 中，$b_2^2b_3$ 的系数是 $|\{i\in B:i\ge3\}|$，前提是 $B\subset R$，否则为零。因此上表给 $6$。计算基 Fano 参考中，只有 236、456 两项有贡献，参考系数是 $2+3=5$。这里的下标从 0 起。

对这个系数，五个正权重是击穿参考值所需的最小支持。先删除所有系数为零的三元组，再将 $B\subset R$ 化为补边。图上的约束包含顶点度至多 1 与每个三角形的总权至多 1。若至多四条边且没有三角形，图为二分图，较小的一侧至多有两个顶点，故总权至多 2。若有三角形，其总权至多 1，且至多另有一条边，额外权重也至多 1。两种情况下系数均为 $2\sum_e w_e+\deg_w(2)\le5$。五环以最小支持达到组合最优 6，因为总权至多 $5/2$，且 $\deg_w(2)\le1$。线性规划用于定位见证，以上检查只涉及精确的半整数。

## 物理补全给出的严格排除

取任意正交归一的两腿 $x,y$，令 $E=\operatorname{span}\{x,y\}^\perp$，并取 $E$ 的完整标准正交基 $(u_i)_{i\in J}$。用 $p_{xyij}=\|\Pi_F(x\wedge y\wedge u_i\wedge u_j)\|^2$ 表示对应四腿权重。对任一奇数大小的指标集 $S\subseteq J$，有

$$
\sum_{i\in S,\,j\in J\setminus S}p_{xyij}\ \ge\ \frac q3 .
$$

结合 Theorem 17 的精确三腿补全 $\sum_{j\ne i}p_{xyij}=q$，得到 $\sum_{i<j\in S}p_{xyij}\le (|S|-1/3)q/2$。若上面的半权五环可由某个物理标架实现，取 $x=u_0$、$y=u_1$、$S=R$，每个残余顶点的内部补全权重都等于 $q$，故没有任何外部补全。这会违反泄漏下界。五环要求内部和为 $5q/2$，而下界给出内部和至多 $7q/3$。[Sierant，Appendix C.1，Corollary 2 和 Theorem 17](https://arxiv.org/html/2609.13106v2)

### 泄漏下界证明

写 $m=d/2$。先沿计算基差值 1 构造斜二形式

$$
\omega_{1,\chi}=\sum_{j\in\mathbb F_2^{n-1}}\chi(j)\,e_{2j}\wedge e_{2j+1},
\qquad \chi\in\widehat{\mathbb F_2^{n-1}}.
$$

这里 $\chi(j)\in\{\pm1\}$。其斜系数矩阵是 $m$ 个 $2\times2$ 酉斜块的直和，故为酉矩阵。沿每个非零差值 $w$，用一个线性 Clifford 坐标置换把差值 1 送到 $w$，得到 $\omega_{w,\chi}$。同一 $w$ 下的 Walsh 函数正交，不同 $w$ 的边支撑不交，故全部 $\omega_{w,\chi}$ 是 $\Lambda^2\mathbb C^d$ 的正交基，各自楔积范数平方为 $m$。因此对任意正交归一的 $x,y$，

$$
\sum_{w,\chi}|a_{w,\chi}|^2=m,\qquad
a_{w,\chi}=\langle x\wedge y,\omega_{w,\chi}\rangle .
$$

令 $\psi_{w,\chi}=\omega_{w,\chi}\wedge\omega_{w,\chi}/2$。当 $w=1$，每个含方向 1 的平面由两条相邻标签边组成。它作为升序楔积的系数为 $\chi(j)\chi(j\oplus h)=\chi(h)$，其中 $h\ne0$ 是平面方向在商空间中的非零元素。故系数在每个平行类恒定，$\psi_{1,\chi}$ 位于 $W_F$。对 $\chi$ 求外积和时，Walsh 正交性消去不同方向间的项。在 $\psi_L=\sqrt q\sum_{F\parallel L}e_F$ 的归一化下，

$$
\sum_{\chi}|\psi_{1,\chi}\rangle\langle\psi_{1,\chi}|
   =\frac m q\sum_{L\ni1}|\psi_L\rangle\langle\psi_L|.
$$

线性 Clifford 置换给出每个 $w$ 的同一式子，它在 $W_F$ 中把每个平行类基向量送到对应基向量乘整体符号。每个平面方向有三个非零差值，因而

$$
\sum_{w,\chi}|\psi_{w,\chi}\rangle\langle\psi_{w,\chi}|
   =\frac{3m}{q}\Pi_F .
$$

现固定一项 $\omega$，略去指标。令 $a=\langle x\wedge y,\omega\rangle$，$\beta=a_ya_x(\omega\wedge\omega/2)$，其中 $a_y,a_x$ 是 Hermitian 内乘。若 $a\ne0$，在标架 $x,y,E$ 中写

$$
\omega=a\,x\wedge y+x\wedge v+y\wedge z+\eta,\qquad
\beta=a\,\eta-v\wedge z .
$$

所以 $\beta$ 的斜矩阵是 $\omega$ 的矩阵对前两腿进行 Schur 补后的 $a$ 倍。Schur 补的逆是原酉矩阵逆的主压缩，算子范数至多 1。因此 $\beta$ 在 $E$ 上的最小奇异值至少为 $|a|$。当 $a=0$ 时，下文的单项下界自然成立。

奇维 $S$ 上的斜主块有单位核向量。沿该向量，$\beta$ 的输出完全落在补块，模长至少 $|a|$。因此 $S$ 与补块之间的单个矩形块的 Frobenius 范数平方至少为 $|a|^2$。用上面的紧框架恒等式对所有 $\psi_{w,\chi}$ 求和，即得

$$
\frac{3m}{q}\sum_{i\in S,\,j\in J\setminus S}p_{xyij}
=
\sum_{w,\chi}\sum_{i\in S,\,j\in J\setminus S}
 \left|\langle x\wedge y\wedge u_i\wedge u_j,\psi_{w,\chi}\rangle\right|^2
\ge\sum_{w,\chi}|a_{w,\chi}|^2=m.
$$

该约束排除精确五环见证。它给出的五顶点内部上界为 $7q/3$，尚未达到把该系数压回计算基参考值所需的 $2q$。

## 加入 $7q/3$ 后的组合放松仍不足以覆盖全谱

将表中的五个权重同时换成 $7/15$，另加 $x_{016}=1$。点对上界仍成立：五环支持的每对权重至多 $14/15$，且 $016$ 只含一个 $R$ 的标签。每个四点集要么只有五环支持的至多两个三元组，要么只含外加的 $016$。有序行中，若 $016$ 有贡献且固定的存在标签在 $R$，则它是 6，被排除的标签位于 $R\setminus\{6\}$。五环项必须对应一条与被排除标签相连的边，至多两项，所以有序行总和至多 $1+14/15<2$。存在标签为 0 或 1 时只可能由 $016$ 贡献。没有 $016$ 的行至多有 $R$ 中一个标签的三项贡献。每个五点集的权重至多 $7/3$：不含 $016$ 时由总五环权重给出，含 $016$ 时至多再含一条全位于 $R$ 的三元组。

在逆谱 $(1,1,R_*,R_*,R_*,R_*,R_*)$ 上，该可行数组值为 $(7/3)R_*^3+R_*$，超过 Fano 参考 $2R_*^3+4R_*^2+R_*$ 当且仅当 $R_*>12$。这是补上 $7/3$ 上界后，对当前线性放松的精确障碍。没有构造实际量子标架。
