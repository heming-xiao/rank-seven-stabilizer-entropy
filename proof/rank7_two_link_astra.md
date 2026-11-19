# Schmidt 秩七的固定二平面五顶点不等式

2026-11-17。以下两个充分条件均允许五维空间在整个物理空间中任意取向。一般固定二平面的结论仍未证明。

## 定义

取物理维数 $d=2^n\ge8$，$q=4/d$。给定二平面 $X=\operatorname{span}(x,y)$ 的任意正交归一基以及 $Y\subset R=X^\perp$ 中的五维空间，记

$$
  B(X,Y)=q^{-1}\sum_{i<j}\|\Pi_F(x\wedge y\wedge u_i\wedge u_j)\|^2
       =\operatorname{Tr}(K_X\,\Lambda^2 P_Y),\quad
  K_X=q^{-1}\sum_L |a_ya_x\psi_L\rangle\langle a_ya_x\psi_L|.
$$

$u_i$ 是 $Y$ 的任意标准正交基，$a_v$ 是以厄米内积收缩 $v$ 的湮灭算子。定义与两组基的选取无关。所求为 $B(X,Y)\le2$。以下使用 [Sierant 的 Corollary 2、Theorem 17、Corollary 4](https://arxiv.org/html/2609.13106v2)。

## 命题一　固定二平面含一个稳定子态

若 $X$ 含任意纯稳定子态，则 $B(X,Y)\le2$。$X$ 的另一方向可以具有遍及整个物理空间的计算基支撑。

**证明。** Clifford 共轭保持 $\Pi_F$，可取 $x=e_0$。Corollary 2 给出 $q^{-1/2}a_x\psi_L=\pm e_{T_L}$，其中 $T_L=L\setminus\{0\}$。这些三元组构成非零坐标标签上的 Steiner 三元系。每对不同点 $a,b$ 恰属于三元组 $\{a,b,a\oplus b\}$。

写 $V_5=Y$，$V_6=Y\oplus\mathbb C y$。由
$\Lambda^3 V_6=\Lambda^3 V_5\oplus(y\wedge\Lambda^2 V_5)$ 的正交分解，

$$
 B(X,Y)=\sum_T\big[\langle e_T,\Lambda^3 P_{V_6}e_T\rangle
                          -\langle e_T,\Lambda^3 P_{V_5}e_T\rangle\big].
$$

对秩 $k$ 的空间 $V_k$，以其单位体积元 $\Omega_k$ 的坐标概率 $\Pr(S_k=S)=|\langle e_S,\Omega_k\rangle|^2$ 抽取 $k$ 个标签。若 $U$ 为 $V_k$ 的标准正交列矩阵，则这些概率是 $|\det U_S|^2$，和为一。Cauchy–Binet（或先收缩体积元再取坐标平方和）给出对任意 $T$ 的包含概率
$\Pr(T\subset S_k)=\det(P_{V_k})_{T,T}=\langle e_T,\Lambda^{|T|}P_{V_k}e_T\rangle$。

这两个分布可以耦合为 $S_5\subset S_6$。给出有限维证明。对五子集族 $\mathcal D$，记 $N(\mathcal D)$ 为包含该族某个成员的六子集全体，$P_{\mathcal D},P_{N(\mathcal D)}$ 为相应坐标楔投影。定相使 $a_y\Omega_6=\Omega_5$。收缩只删去一个坐标，故

$$
  \Pr(S_5\in\mathcal D)=\|P_{\mathcal D}a_yP_{N(\mathcal D)}\Omega_6\|^2
           \le \|P_{N(\mathcal D)}\Omega_6\|^2=\Pr(S_6\in N(\mathcal D)).
$$

使用了 $\|a_y\|\le1$。这是有限二分包含图的加权 Hall 条件。由最大流最小割定理，存在总流量一、两侧边际为上述两分布的非负流，给出所需耦合。每个样本记 $r=S_6\setminus S_5$ 中唯一的标签。新增的 Steiner 三元组都含 $r$，其余两点在 $S_5$ 中构成两两顶点互异的边，因此新增至多 $\lfloor 5/2\rfloor=2$ 个。取期望即得命题。

同一证明对任意 $k=\dim Y$ 给出上界 $\lfloor k/2\rfloor$。

## 命题二　固定二平面支撑在一个八点仿射空间

若存在八点仿射三空间 $H\subset\mathbb F_2^n$ 使 $X\subset\mathbb C^H$，则 $B(X,Y)\le2$。Clifford 共轭后的任意此类 $X$ 也满足结论。

**收缩算子的块分解。** 设 $D=\operatorname{dir}H$。在 $R$ 中取正交分解，一块为 $R_H=\mathbb C^H\ominus X$（维数六），其他块为各平行陪集 $C\ne H$ 的 $\mathbb C^C$（维数八）。对一个二维方向 $L$，$\psi_L=\sqrt q\sum_{F\parallel L}e_F$。若 $\dim(L\cap D)=0$，每个 $F$ 与 $H$ 至多交于一点，故双收缩为零。若 $L\subset D$，有贡献的平面都在 $H$ 内，结果属于 $\Lambda^2 R_H$。若 $\dim(L\cap D)=1$，有贡献的 $F$ 在 $H$ 内有两点，剩余两点都在同一个陪集 $C=H+v$，其中 $v\in L\setminus D$。这个陪集对给定 $L$ 唯一。因此各个 $a_ya_x\psi_L$ 都属于单个 $\Lambda^2 R_b$，$K_X=\bigoplus_b K_b$，在不同块的混合楔积上为零。

**块内的边权。** 在每个 $R_b$ 任取标准正交基 $f_i$，置 $p_{ij}=\langle f_i\wedge f_j,K_b(f_i\wedge f_j)\rangle\ge0$。Theorem 17 对三向量 $x,y,f_i$ 的一粒子补全和等于 $q$，所以 $\sum_{j\ne i}p_{ij}=1$。这里其他块的补全项全为零。对任意三个块内顶点 $i,j,k$，Corollary 4 应用于五维空间 $\operatorname{span}(x,y,f_i,f_j,f_k)$。五项非负和至多为 $q$，保留含 $x,y$ 的三项得 $p_{ij}+p_{ik}+p_{jk}\le1$。

令 $m=\dim R_b\in\{6,8\}$，用 $e(A)=\sum_{i<j\in A}p_{ij}$ 记内部边权。对任意顶点子集 $A$，对两侧分别加总顶点度，消去割边，得到

$$
 e(A)-e(A^c)=|A|-m/2.
$$

偶数大小集合由度数和满足 $e(A)\le |A|/2$。奇数大小 $1,3$ 的行由空和及三角行给出。块内大小 $5,7$ 的可行奇集的补集大小只可能是 $1,3$，故补集恒等式给 $e(A)\le\lfloor |A|/2\rfloor$。这已覆盖所有块内子集。

**跨块的任意五维空间。** 对每个块 $R_b$，在块内选基令 $P_b P_Y P_b|_{R_b}$ 对角，特征值写为 $s_i$。楔积的函子性给出 $P_{\Lambda^2 R_b}(\Lambda^2 P_Y)|_{\Lambda^2 R_b}=\Lambda^2(P_bP_YP_b|_{R_b})$。因此

$$
 B(X,Y)=\sum_b\sum_{i<j\in b} p_{ij}s_i s_j.
$$

在所有块的联合基中，按 $Y$ 的体积元取恰含五个标签的随机集合 $S$。同块两点 $i,j$ 的包含概率为 $P_Y$ 相应二阶主子式，即 $s_i s_j$。不要求不同块独立。令 $S_b=S\cap b$，则逐样本有

$$
 B(X,Y)=\mathbb E\sum_b e(S_b)
 \le \mathbb E\sum_b\lfloor |S_b|/2\rfloor\le\lfloor5/2\rfloor=2.
$$

这也给出任意 $\dim Y=k$ 时的 $\lfloor k/2\rfloor$ 界。在二平面由同一仿射三空间内任意两根计算基向量张成时，取 $Y$ 含两个完整的配对和一个额外方向可达等号。

## 一般旗标的精确缺口

对任意单位 $x$，定义 $J_x=q^{-1}a_x\Pi_F a_x^\dagger|_{\Lambda^3 x^\perp}$。Theorem 17 的 uniform occupation 表明 $J_x$ 是正交投影。任意 $x,y,Y$ 仍精确满足

$$
 B(X,Y)=\operatorname{Tr} J_x(\Lambda^3 P_{Y\oplus\mathbb C y}-\Lambda^3 P_Y).
$$

记 $g_{L,F}=a_x e_F$。$J_x=\sum_L\sum_{F,F'\parallel L}|g_{L,F}\rangle\langle g_{L,F'}|$，其中 $F,F'$ 分别遍历方向 $L$ 的各仿射平面。对锚点 $x=e_0$，每个 $L$ 只有一个非零 $g_{L,F}$，且是单个三坐标楔。一般的 $x$ 产生平行但彼此不交的 $F\ne F'$ 间的相干项，同一平面内部也可能含多个三坐标楔。体积元的单一坐标概率只控制对角项。命题二利用双收缩后每个方向只进入唯一的维数至多八的块避开这个问题。超过八维后，仅有块内度及三角约束不足以用取补证明大小五的奇集行。

上述两个证明均未估计一般相干项，也未给出违反 $B\le2$ 的旗标。它们没有解决全尺寸秩七。
