# 两级秩七谱的移位系数与双线性 Pauli 缺陷

2026-11-17。令排序 Schmidt 概率为 \((1,1,r,r,r,r,r)\)，整体缩放不改变轨道比较。下文给出归一的重叠增益、原线性证书的精确极值，以及从最高秩二谱投影输运到完整谱的 Pauli 缺陷。与四楔压缩余量合并，这独立给出一个任意维数的内部谱条件。

## 重叠增益和原约束的端点

记 \(X,Y\) 为二重最高和五重次高子空间，\(C=P_X+rP_Y\)、\(N=C^{1/2}\)、\(q=4/d\)。对七个正 Schmidt 标签的四元组 \(A\)，令 \(x_{[7]\setminus A}=\|\Pi_F u_A\|^2/q\)。用 \(X_j\) 表示含恰好 \(j\) 个最高标签的补三元组总权，故 \(X_0=V=B(X,Y)\)，排序参考为 \((2,4,1)\)。低尾标签对容量和、双高标签对容量分别给 \(3X_0+X_1\le10\) 与 \(X_2\le1\)。因此当 \(0<r\le1/3\)，

\[
\begin{aligned}
[c_F(C)-c_F(C_{\rm CB})]/q
  &=r^2[(X_0-2)+r(X_1-4)+r^2(X_2-1)]\\
  &\le r^2(1-3r)(V-2).
\end{aligned}
\]

还可精确保留三类对容量的未饱和项。设 \(\delta_{LL},\delta_{HL},\delta_{HH}\) 分别为低低、高低、高高标签对中 \(1-\sum_{B\supset e}x_B\) 的总和，则

\[
\frac{c_F(C)-c_F(C_{\rm CB})}{qr^2}
=-\tfrac13\delta_{LL}+\tfrac{1-3r}{6}\delta_{HL}
  +[r(1-r)-\tfrac13]\delta_{HH}.
\]

这是三类对分别被每个三元组计数后解线性方程的结果。若只保留原点对、四点和有向约束，可将变量按两个高标签与五个低标签的独立置换平均。令 \(a,b,c\) 为补三元组内高标签数分别为 \(0,1,2\) 时的单项权重。目标为 \(r^2(10a+20rb+5r^2c)\)。容量行给 \(a\le1/4,\ 3a+2b\le1,\ c\le1/5\)。当 \(r\le1/3\) 时这已证明松弛最大值至多 \(r^2(5/2+(5/2)r+r^2)\)。\((a,b,c)=(1/4,1/8,1/5)\) 达此值。其余各轨道行是 \(4b+c\le1\)，\(a+3b\le1\)，\(2b+2c\le1\)，\(10b\le2\)，\(6b+4c\le2\)，\(6a+4b\le2\)，\(3a+6b+c\le2\)，逐项满足。这个松弛的最大值严格超过排序参考，除非 \(r=1/3\)。该可行点只属于线性松弛。[容量行与原系数证书](rank7_ambient_reduction.md)

## 交换子给两个谱槽的缺陷输运

对 Hermitian 算子 \(A,B\)，定义非负对称双槽量

\[
J(A,B)=d^{-2}\sum_{a,b:[a,b]=1}\operatorname{Tr}(A W_a)^2\operatorname{Tr}(B W_b)^2.
\]

这里求和按有序对。Pauli Parseval 给

\[
J(A,B)=\frac1{4d}\sum_a \operatorname{Tr}(A W_a)^2\|[B,W_a]\|_{\rm HS}^2.
\]

记 \(P=P_X\)。在 \(C\) 的本征基逐矩阵元比较，两类谱只要跨越 \(P\) 的边界便至少相差 \(g=1-r\)。这给任意 \(W\) 的 \(\|[C,W]\|_{\rm HS}^2\ge g^2\|[P,W]\|_{\rm HS}^2\)，不需要 \(W\) 属于某个稳定子群。先比较第二槽，再利用对称性比较第一槽，得

\[
J(C,C)\ge g^2 J(C,P)=g^2J(P,C)\ge g^4 J(P,P).
\]

实际上若 \(S=P_X+P_Y\)，三个谱块上的差值平方还给 \(J(C,C)\ge g^4J(P,P)+2g^2r^2J(P,S)+r^4J(S,S)\)。这是从 \((\lambda_i-\lambda_j)^2\ge g^2(P_i-P_j)^2+r^2(S_i-S_j)^2\) 对两个槽分别应用相同论证所得。

令 \(\eta(A)=\Delta_d(A)/d\)。Theorem 14 的投影为收缩，按每条无序反对易边只出现一次，故 \(2J(A,A)\le\eta(A)\le10J(A,A)\)。又 \(\Lambda^4P=0\)、\(\operatorname{Tr}P^2=\operatorname{Tr}P^4=2\)，所以 \(\eta(P)=8-F_P(P)/d=8\delta\)，其中 \(\delta\) 是秩二稳定性笔记的同一四次矩缺口。应用已证 \((V-2)_+\le20\delta\) 得

\[
\eta(C)\ge \frac{g^4}{5}\eta(P)\ge \frac{2}{25}(1-r)^4(V-2)_+.
\]

这个支付对任何 \(r\) 成立，且不依赖于最大 Pauli 标签数、舍入门槛或环境维数。[秩二稳定性](rank7_rank2_stability_route.md) · [原文 Theorem 14](https://arxiv.org/html/2609.13106v2)

## 与四楔压缩余量相加

设 \(T=q^{-1}P_{\Lambda^4S}\Pi_F P_{\Lambda^4S}\) 作用于七维正支撑的四外积，\(A=\Lambda^4N\) 限制于同一空间。Theorem 7 给 \(0\preceq T\preceq I\)。归一化压缩余量为

\[
\frac{q c_F(C)-Q_F(N)}{q^2}
 =\operatorname{Tr}[A^2(T-T^2)]+\frac12\|[A,T]\|_{\rm HS}^2.
\]

令 \(E\) 是双高标签四楔的谱子空间投影，\(B=ETE|_E\)。该块的 \(A\) 本征值为 \(r\)，其它两个块为 \(r^{3/2},r^2\)。令 \(w=r^2(1-\sqrt r)^2\)。第一项至少为 \(w\operatorname{Tr}E(T-T^2)\)，第二项至少为 \(w\|ET(I-E)\|_{\rm HS}^2\)。相加给 \(w\operatorname{Tr}(B-B^2)\)。这里 \(B\) 是效应算子且 \(\operatorname{Tr}B=V\le7/3\)。若 \(V=2+v>2\)，固定总迹时平方和在两个本征值为 1、第三个为 \(v\)、其余为 0 的最集中列表上最大，故 \(\operatorname{Tr}(B-B^2)\ge v(1-v)\ge(2/3)v\)。若 \(V\le2\)，余量本来非负。[五点泄漏界](rank7_fractional_cycle.md)

实际主目标保留这两个独立非负余量。Proposition 2 给 \(G-G_{\rm CB}\le42d(c_F-c_{F,\rm CB})-6d^2(qc_F-Q_F)-\eta(C)\)。代入 \(dq=4\)，所以一个任意维数的充分条件为

\[
168r^2(1-3r)\le 64r^2(1-\sqrt r)^2+\frac{2}{25}(1-r)^4,
\qquad 0<r\le\tfrac13.
\]

去掉末项已覆盖 \(r\ge[(8+\sqrt{987})/71]^2\) 至 \(1/3\)。保留末项使该端点严格向下延伸，同时其大小仍不足以覆盖 \(r=1/5\)。通过原文 Lemma 1 与纯稳定子辅助位补齐，单酉界得到任意尺寸二分割上的排序计算基全局最优性。[原文 Lemma 1、Proposition 2、Theorem 7](https://arxiv.org/html/2609.13106v2)

## 对称扇区与混合扇区付的是同一个投影缺陷

以下恒等式对任意正算子 \(C=N^2\) 成立，不需要两级谱。令 \(c_a=\operatorname{Tr}(CW_a)\)，在两副本空间上定义

\[
L(C)=d^{-2}\sum_{a,b:[a,b]=1}c_a c_b\,W_a\otimes W_b,
\qquad L_-(C)=L(C)|_{\Lambda^2}.
\]

这里按有序对计，因而 \(L(C)\) 与副本交换 \(S_{12}\) 对易，\(\|L(C)\|_{\rm HS}^2=J(C,C)\)。在反对称 Pauli 正交基 \(E_a=W_a/\sqrt d\) 中，对 Hermitian 矩阵定义实线性对合 \(\mathcal J(K)_{ab}=(-1)^{[a,b]}\overline{K_{ab}}\)。则

\[
(I-\mathcal J)K(C)=2L_-(C),\qquad
\mathcal R_d(K(N))=\tfrac12\|L_-(C)\|_{\rm HS}^2.
\]

为检验首个等式，把矩阵元 `Tr(W_a C W_b C^T)/d` 展开成四 Pauli 迹。任一非零项总标签为零，即 `a+s+b+t=0`。复共轭倒转 Pauli 顺序，其交换符号指数为 `[a,b]+[s,t]`。例如把末项 `t` 先穿过其余三项，符号指数 `[t,a+s+b]=0`，再倒转前三项即得所述指数。外乘 `(-1)^[a,b]` 后，\(I-\mathcal J\) 仅留下反对易 `s,t` 的项并乘二，等于两腿 Pauli 展开的反对称限制。第二式来自 Hermitian 的两个非对角矩阵元各贡献 `4 ρ_ε²`，对角贡献零。[原文 Eqs. (140)–(146)](https://arxiv.org/html/2609.13106v2)

还可以把 \(L_-(C)\) 的范数直接读为 Theorem 14 的边块。由交换迹恒等式，

\[
\operatorname{Tr}(S_{12}L(C)^2)
=\frac{4}{d^3}\sum_{s\ne0}z_s^{\mathsf T}(I-A_s)z_s.
\]

具体地，只有两个反对易无序边具有同一和标签时四 Pauli 迹才非零。任一边的两种顺序给同号，故有因子四。同一边交错乘积的迹为 \(d\)。不同边的交错乘积 `W_a W_c W_b W_e` 在四循环中比循环顺序多一个反对易交换，故迹为 `−d ε_F`。这在 `[a,c]=0` 和 `[a,c]=1` 的两种情况下分别通过交换 `c,b`，或将 `c` 越过 `e,b` 复核。由原文 \(I-A_s=(d/2)(I-2\mathsf Q_s)\)，交换的负谱部分给

\[
\|L_-(C)\|_{\rm HS}^2
=\tfrac12[\|L(C)\|_{\rm HS}^2-\operatorname{Tr}(S_{12}L(C)^2)]
=\frac{2}{d^2}\sum_{s\ne0}\|\mathsf Q_s z_s\|^2.
\]

因此 Eq. (175) 的缺陷可以合并写成

\[
\mathcal D(N)=d^2D_{\rm sym}(N)+4d\mathcal S_d(K(N))
  +2J(C,C)+24\|L_-(C)\|_{\rm HS}^2 .
\]

具体地，\(\Delta_d(C)/d\) 支付 \(2J+8\|L_-\|_{\rm HS}^2\)，而混合扇区的 \(\mathcal R_d\) 再支付 \(16\|L_-\|_{\rm HS}^2\)。上面的交换子输运控制 \(J\)，尚未对 \(L_-\) 建立同样的谱输运下界。[原文 Eqs. (104), (109), (146), (175)](https://arxiv.org/html/2609.13106v2)

## 秩二时混合投影缺陷单独判定稳定子性

当 \(P\) 是秩二投影，令 \(\alpha\) 是其单位可分解二楔，\(f_a=\langle E_a,\alpha\rangle\)。于是 \(K(P)=ff^*\)。每个 \(E_a\) 是斜酉矩阵对应的二形式除以 \(\sqrt{d/2}\)，故可分解性给 \(|f_a|^2\le2/d\)。另有

\[
\|L_-(P)\|_{\rm HS}^2
=\tfrac12\left(1-\tfrac d2\sum_a |f_a|^4\right).
\]

事实上，令 \(R_{ab}=(-1)^{[a,b]}\)。从 \(2L_-=(I-\mathcal J)(ff^*)\) 得平方范数为 \([1-(f^{\circ2})^*R(f^{\circ2})]/2\)。原文楔平方 Gram 恒等式给 \(R=(d/2)I-(3d/2)\mathsf P_F\)。因为 \(\alpha\wedge\alpha=0\)，对四楔作 Pauli 平均只留下同标签项，因而 \(G f^{\circ2}=0\)，即 \(\mathsf P_F f^{\circ2}=0\)。[原文 Eqs. (154)–(157)](https://arxiv.org/html/2609.13106v2)

进一步，\(L_-(P)=0\) 当且仅当 \(P\) 是四次矩饱和的秩二稳定子编码。证明正向时在 \(f\) 的支撑中固定 \(a_0\)。\(\mathcal J(ff^*)=ff^*\) 表明各非零对的相位差之二由 \((-1)^{[a,b]}\) 决定。把任意 \(a,b\) 先各自与 \(a_0\) 比较，再相互比较，得到 \([a+a_0,b+a_0]=0\)。故支撑在某个各向同性仿射陪集 \(a_0+U\)，且整个陪集的二次型 \(q(a)=x_a\cdot z_a\) 均为 1。后者因为 \(q(u)+[a_0,u]\) 在各向同性 \(U\) 上是线性的，并对生成元为零。

若 \(U\) 最大各向同性，则 \(q\) 在每个陪集内为仿射函数，且恰有一个陪集上的函数为常数。其它陪集的二次符号和为零。全空间 Gauss 和为 \(+d\)，故那个常数必须是 0，与此处矛盾。因此 \(\dim U\le n-1\)。由 \(|f_a|^2\le2/d\) 和总权重 1，支撑至少 \(d/2\) 个元素，故 \(\dim U=n-1\)。对每个 \(u\in U\)，原文 Eq. (147) 表明 \(\Lambda^2 W_u\) 在 \(\alpha\) 上作用为 \((-1)^{q(u)+[u,a_0]}=+1\)。于是 \(W_u\) 保持原二平面，在其中的行列式为 \(+1\)，故两个本征符号相同。其公共字符空间的维数恰为二，正是 \(P\)。反向时 \(P\) 的 Pauli 支撑对易，因此 \(L(P)=0\)。[原文 Eq. (147)](https://arxiv.org/html/2609.13106v2)

## 两级谱的完整混合投影估计

令 \(E_H,E_M,E_L\) 分别是二外积上 \(\Lambda^2X,X\wedge Y,\Lambda^2Y\) 的正交投影。取矩阵相对于反对称 Pauli 基，定义实 HS 空间的正交投影 \(\mathcal B=(I-\mathcal J)/2\)。置

\[
u=\mathcal B E_H,\qquad v=\mathcal B E_M,\qquad w=\mathcal B E_L.
\]

则 \(L_-(C)=u+rv+r^2w\)。令 \(m=d/2\)，以 \(\langle h\rangle=m^{-1}\sum_a h_a\) 表示标度和，置 \(p_a=m(E_H)_{aa}\)、\(k_a=m(E_M)_{aa}\)、\(s_a=m(E_L)_{aa}\)。每个归一反对称 Pauli 来自斜酉二形式除以 \(\sqrt m\)。在以 \(X,Y\) 为分块的新坐标基上，原斜矩阵经酉合同仍为斜酉。故逐项有

\[
0\le p_a\le1,\quad k_a\le2(1-p_a),\quad s_a\le2,
\quad p_a+k_a+s_a\le3,
\quad \langle p\rangle=1.
\]

第二式来自两根 \(X\) 腿上斜矩阵行平方和，最高二楔在两行各占 \(p_a\)。第三和第四式用奇数维斜主压缩的偶数秩，算子范数至多一。最后一式是秩一投影迹。记 \(\kappa=\langle p(1-p)\rangle\) 与 \(z=\langle pk\rangle\)，于是 \(0\le z\le2\kappa\)，并且 \(\langle ps\rangle\le\min(2,2+\kappa-z)\)。后一界把 \(p+k+s\le3\) 乘 \(p\) 后求和，并用 \(\langle p^2\rangle=1-\kappa\)。

精确极化给三个内积

\[
2\|u\|^2=\kappa,\quad
2\langle u,v\rangle_{\rm HS}=-\langle pk\rangle,\quad
2\langle u,w\rangle_{\rm HS}=V-\langle ps\rangle .
\]

为检查最后一式的外积因子，对任意 Hermitian \(K\) 使用

\[
2\|\mathcal B K\|_{\rm HS}^2=\operatorname{Tr}K^2
-\tfrac d2\sum_a K_{aa}^2+\tfrac{3d}{2}\operatorname{Tr}[\mathsf P_F(K\circ K)].
\]

来源是 \(R=(d/2)I-(3d/2)\mathsf P_F\) 与 \(\mathcal J\) 的矩阵定义。若 \(f,g\) 为两个二楔 \(\alpha,\beta\) 的反对称 Pauli 系数，\(G(f\circ g)=\frac12\Pi_F(\alpha\wedge\beta)\)，其中右边使用坐标单位楔的标准外积。Pauli 四次平均只保留同框架标签，而系数 \(1/2\) 来自原文 Eq. (154) 的楔平方约定。可在标准坐标二形式上由原文的斜矩阵归一化核算，等价地原文 \(\|E_a\wedge E_a\|^2=(d-2)/(2d)\)，标准单位楔的对应值为 \(2(d-2)/d\)。故 \(\operatorname{Tr}(\mathsf P_F(E_H\circ E_L))=(2/3)(1/4) qV=qV/6\)。对 \(E_H\circ E_M\) 同一追迹为零，因为普通楔中重复一根 \(X\) 腿。代入极化中的交叉系数，利用 \(dq=4\) 得所列三个内积。[原文 Eqs. (154)–(157)、(169)](https://arxiv.org/html/2609.13106v2)

现在若 \(V>2\)，记 \(\nu=V-2\)。有

\[
\begin{aligned}
2\langle u,L_-(C)\rangle_{\rm HS}
&\ge \kappa-rz+r^2[\nu+\max(0,z-\kappa)]\\
&\ge (1-r)^2\kappa+r^2\nu.
\end{aligned}
\]

末行来自 \(z\in[0,2\kappa]\)，因为第一行的右侧随 \(z\) 不增。该不等式也说明当 \(V>2\) 时 \(\kappa>0\)。Cauchy–Schwarz 和算术几何平均给

\[
\|L_-(C)\|^2_{\rm HS}
\ge \frac{[(1-r)^2\kappa+r^2\nu]^2}{2\kappa}
\ge 2r^2(1-r)^2\nu.
\]

若 \(V\le2\)，用右端为零的版本即可。将此式乘缺陷中的系数 24，再加四楔压缩余量，一个充分条件是

\[
168(1-3r)\le64(1-\sqrt r)^2+48(1-r)^2,
\qquad 0<r\le\tfrac13 .
\]

它对 \(r\in[1/4,1/3]\) 成立。令 \(z=\sqrt r\)，右减左是 \(8(6z^4+59z^2-16z-7)\)，在 \(z=1/2\) 等于 1，且在 \(z\ge1/2\) 单调增加。其唯一正根在 \((0,1/2)\) 并给出稍低的精确端点。由于原有谱锥覆盖 \(r\ge1/3\)，这证明两级概率谱 \((1,1,r,r,r,r,r)\) 对全部 \(r\in[1/4,1]\) 和任意量子比特二分割的排序计算基最优性。尚可加入 \(2J(C,C)\) 的独立支付，前面四楔余量中也未保留所有正项。[主目标归约](rank7_two_level_defect_route.md) · [原文 Lemma 1、Proposition 2、Theorem 7](https://arxiv.org/html/2609.13106v2)

## 两个最高概率可不同

同一证明给出谱 \((a,b,r,r,r,r,r)\) 的两个参数条件。假设 \(a\ge b\ge r>0\)、\(a\ge3r\)。令 \(X=\operatorname{span}(x_0,x_1)\)、\(Y=X^\perp\cap\operatorname{ran}C\)，并将前面的混合项 \(E_M\) 分成 \(E_{M_i}=P_{x_i\wedge Y}\)。其单行对角概率 \(k_{i,a}\le1-p_a\)，故 \(z_i=\langle p k_i\rangle\le\kappa\)。三腿块原有奇数斜约束给 \(\langle ps\rangle\le\min(2,2+\kappa-z_0-z_1)\)。谱分配现为

\[
K(C)=ab E_H + ar E_{M_0} + br E_{M_1} + r^2 E_L.
\]

前述极化分别给每个 \(E_{M_i}\) 的负交叉项，故当 \(\nu=V-2>0\)，

\[
2\langle u,L_-(C)\rangle_{\rm HS}
\ge ab\kappa-r(az_0+bz_1)+r^2[\nu+\max(0,z_0+z_1-\kappa)]
\ge(a-r)(b-r)\kappa+r^2\nu.
\]

第一个下界的右端对 \(z_0,z_1\) 都不增，故点 \(z_0=z_1=\kappa\) 给最后的下界。与双等头情形相同，这给 \(\|L_-(C)\|_{\rm HS}^2\ge2(a-r)(b-r)r^2\nu\)。

令 \(X_{1,i}\) 为含 \(x_i\) 但不含另一头腿的四楔总重叠权。各有 \(X_{1,i}\le2\)，恰是相应有向旧约束。低尾点对约束仍给 \(3V+X_{1,0}+X_{1,1}\le10\)，双高点对容量仍有 \(X_2\le1\)。因此

\[
\begin{aligned}
\frac{c_F(C)-c_{F,\rm CB}}{q}
&=ab r^2(V-2)+ar^3(X_{1,0}-2)+br^3(X_{1,1}-2)+r^4(X_2-1)\\
&\le b r^2(a-3r)(V-2).
\end{aligned}
\]

双高四楔的振幅 \(\sqrt{ab}\,r\) 与其它块最高振幅 \(\sqrt a\,r^{3/2}\) 的差平方是 \(a r^2(\sqrt b-\sqrt r)^2\)，四楔压缩支付的证明只需替换这个最小差平方。于是两个最高概率可不同的充分条件是

\[
168 b(a-3r)\le64a(\sqrt b-\sqrt r)^2+48(a-r)(b-r).
\]

在 \(a=1,r=1/4\) 时，这覆盖 \(b\in[((32+\sqrt{618})/58)^2,1]\)。特别地，满足严格不等式的参数在本谱族中形成开区间，同时允许 \(a>b\)。[有向容量行](reviews/rank7_ambient_independent_review.md)
