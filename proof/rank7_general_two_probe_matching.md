# 任意排序七点谱的条件匹配与两个混合投影

2026-11-18。取七个正 Schmidt 概率，依序写作

$$
(t_0,t_1,t_2,t_3,t_4,t_5,t_6)=(\alpha,\beta,\gamma,a,b,c,d),
\qquad \alpha\ge\beta\ge\gamma\ge a\ge b\ge c\ge d>0 .
$$

以下的 $d$ 只表示末概率，物理 Hilbert 空间维数另记 $D$，$m_0=D/2,\ q=4/D$。本笔记给任意排序谱的两组同时成立的极化不等式，和两者在同一混合范数上的 Gram 公式。证明无须前三根或四条尾根出现简并。

## 四个条件匹配价

七点完全图边 $ij$ 的售价为 $t_it_j$。匹配若在前三点内选边，所选边唯一；以它作为匹配类型，否则记类型为 $\varnothing$。各型最大得分为

$$
\begin{aligned}
 M_{01}&=\alpha\beta+\gamma a+bc,&
 M_{02}&=\alpha\gamma+\beta a+bc,\\
 M_{12}&=\beta\gamma+\alpha a+bc,&
 M_\varnothing&=\alpha a+\beta b+\gamma c.
\end{aligned}
$$

相邻三项差依次为

$$
 \Delta=(\beta-\gamma)(\alpha-a),\qquad
 g=(\alpha-\beta)(\gamma-a),\qquad
 j=(\beta-c)(\gamma-b).
$$

令 $h=b(c-d)$。若一个匹配共有 $k$ 条边，且末标签被使用的指示量是 $\delta$，则各类型的**逐匹配**上界为

$$
 \operatorname{score}\le M_{\rm type}-h(3-k+\delta).
 \tag{1}
$$

**含领先边。** 扣除固定领先边后，自由权重为 $z,a,b,c,d$，其中 $z$ 是剩余的领先概率且 $z\ge a$。完整自由最优价为 $za+bc$。两条自由边且必须使用 $d$ 时，最高为 $za+bd$，因可淘汰的另一顶点中最小为 $c$，余下四个权重按降序邻接配对最优。只有一条自由边时，未用或使用 $d$ 的最高价分别为 $za$ 或 $zd$；损失分别至少为 $h$ 或 $2h$，用 $z(a-d)\ge b(c-d)$ 及 $bc\ge h$。没有自由边时损失至少 $2h$。同时可见未扣减的条件最优确可达。

**不含领先边。** 每条边都至少占一条尾腿。若有三条边且每根领先腿均出现，最佳安排是令前三腿依序与 $a,b,c$ 配对，得 $M_\varnothing$；若还须使用 $d$，最大为 $\alpha a+\beta b+\gamma d$。若只有两根领先腿被使用，余下四根尾腿必全用，对两条领先—尾边及一条尾—尾边，最高为 $\alpha a+\beta b+cd$。例如把较大的尾端从尾—尾边与较小的领先配偶对调，改变量为两项非负差之积，因此可总让 $a,b$ 占据领先腿。与 $M_\varnothing$ 的差是 $c(\gamma-d)\ge b(c-d)$。三边匹配不可能用少于两条领先腿。只有两条边时，无论取的领先腿数，价格至多 $\alpha a+\beta b$，若必须使用 $d$ 则至多 $\alpha a+\beta d$：在每条边选一尾端（若该边含 $d$ 则选 $d$），余端各以两根最高领先腿替代后再降序配对，得界。相较 $M_\varnothing$ 的损失至少分别为 $h$、$2h$。单边在两情形最高为 $\alpha a$、$\alpha d$，损失分别至少 $2h$、$3h$。零边损失至少 $3h$。这证明式 (1)。

独立核验器以七个非负顺序谱差展开式 (1)，对全部 232 个匹配逐项检查多项式的系数均非负，因而覆盖全部连续参数。另以四个整数取值的 120 种降序谱进行了 27,840 条整数比较。[精确核验器](../verification/verify_rank7_four_level_1231_scalar.py)

## 对实际斜 Pauli 坐标极化

每个斜 Pauli 标记对应一个反酉 $J$。在实际七根单位标架中置 $p_{ij}=|\langle x_i,Jx_j\rangle|^2$，$p_1=p_{01},p_2=p_{02},p=p_1+p_2,\ m=p_{12}$，并写

$$
 s_C=\sum_{0\le i<j\le6} t_i t_j p_{ij},
 \qquad s_6=\sum_{0\le i<j\le5}p_{ij},\qquad
 \langle f\rangle=m_0^{-1}\sum_{J\ {\rm skew}} f(J).
$$

对每个 $J$，边权的度至多一，奇集内部和由斜压缩的偶数秩至多为其点数的一半向下取整。Edmonds 匹配定理给边权的随机匹配表示。四个类型的概率是 $p_1,p_2,m,1-p-m$。又 $\mathbb E(k-\delta)=s_6$。将式 (1) 对匹配取平均得到

$$
 s_C\le M_{02}+\Delta p_1-g(1-p)-j(1-p-m)-h(3-s_6).
 \tag{2}
$$

记 $C=N^2$ 为谱概率算子，$L_-=\mathcal B\Lambda^2 C$，$\mathcal B$ 是 Hermitian 矩阵空间上带 Pauli 共轭符号的实正交投影。令 $P_i$ 投到单位二楔 $x_0\wedge x_i$（$i=1,2$），$u_1=\mathcal BP_1$，$u=\mathcal B(P_1+P_2)$。四楔迹的归一权重为 $w_A=\|\Pi_F x_A\|^2/q$。写

$$
 W_i=\sum_{A\supset\{0,i\},\ |A|=4}
           t_{A\setminus\{0,i\}} w_A,\qquad W=W_1+W_2 .
$$

这里 $t_B$ 为标签子集的概率乘积。排序参考中，含 01 的平面为 0123、0145；含 02 的平面为 0123、0246。故

$$
 W_{1,*}=\gamma a+bc,\qquad W_{2,*}=\beta a+bd,\qquad
 W_*=(\beta+\gamma)a+b(c+d).
$$

原混合极化恒等式为 $2\langle u_i,L_-\rangle=t_0t_i+W_i-\langle p_i s_C\rangle$，此处左边取实 Hilbert–Schmidt 内积、角括号求和按上式归一。设 $\kappa=\langle p(1-p)\rangle$、$\kappa_1=\langle p_1(1-p_1)\rangle$、$c_1=\langle p_1(1-p)\rangle$。由 $\langle p_1\rangle=\langle p_2\rangle=1$，又 $M_{01}+M_{02}=\alpha\beta+\alpha\gamma+W_*+h$，把式 (2) 乘 $p$ 求和，再用极化，得到

$$
 2\langle u,L_-\rangle\ge W-W_*+g\kappa+\Delta c_1+
      j\langle p(1-p-m)\rangle-h(\langle p s_6\rangle-5).
 \tag{3}
$$

若已有几何界 $\langle p s_6\rangle\le5+\lambda\kappa$，末项可与 $g\kappa$ 合为 $(g-\lambda h)\kappa$。当 $c=d$，末项恒为零。对单独的最高配对，所有不含 01 的匹配价均至多 $M_{02}$。所以 $s_C\le M_{01}-\Delta(1-p_1)$。又 $M_{01}=\alpha\beta+W_{1,*}$，从而

$$
 2\langle u_1,L_-\rangle\ge W_1-W_{1,*}+\Delta\kappa_1.
 \tag{4}
$$

两项的归一及 $\mathcal B$ 的实内积均沿用[混合扇区恒等式](rank7_two_level_defect_transport.md)。[六坐标的几何估计及物理匹配多面体](rank7_four_level_1231_packing.md)

## 同一混合缺陷的两向量 Gram

由于两根二楔共享 $x_0$，任意两者的楔积为零。由混合投影恒等式的双线性化，

$$
 2\|u\|^2=\kappa,\quad 2\|u_1\|^2=\kappa_1,\quad
 2\langle u,u_1\rangle
   =1-\langle p p_1\rangle=c_1,\qquad
 0\le c_1\le\min(\kappa,\kappa_1).
$$

例如 $2\langle\mathcal BP_1,\mathcal BP_2\rangle=-\langle p_1p_2\rangle$，这是两投影正交且两二楔的楔积为零给出的项。令 $H,H_1$ 是式 (3)、(4) 各自的右端。每个 $\theta\ge0$ 都给一次实际混合缺陷支付

$$
 24\|L_-\|^2\ \ge\
 \frac{12[(H+\theta H_1)_+]^2}
      {\kappa+2\theta c_1+\theta^2\kappa_1}.
 \tag{5}
$$

这是对 $u+\theta u_1$ 使用 Cauchy–Schwarz。若分母为零，该方向为零且分子正部也为零，取零下界。

**剩余步骤。** 正向概率证书将重叠超额分解成 $L_{01}+L_{02}-4$ 与 $L_{01}-2$ 的非负价格组合，式 (3)、(4) 与其配对数一致。任意不同尾概率下，实际的 $W-W_*$ 及 $W_1-W_{1,*}$ 分别加权多个四楔，可能同时亏损。要以式 (5) 处理全谱，还需按同一标架给出两项亏损被线性重叠本身的负项以及四楔压缩损失支付的定量比较，并检验所有连续谱参数。两个匹配价及 Gram 恒等式单独不能作出全谱最优性断言。[原正向证书及其系数](rank7_forward_coefficients_independent.md)
