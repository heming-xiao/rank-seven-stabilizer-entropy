# 共享首腿超额的常数 12 与完整反对易支付

2026-11-18。对任意七根正交物理标架，令 $\nu=L_{01}+L_{02}-4$，令 $P_0$ 是第零根的单粒子投影、$P_3$ 是前三根的单粒子投影，$u=\mathcal B P_{x_0\wedge\operatorname{span}(x_1,x_2)}$ 是共享首腿的混合投影，并记 $\kappa=2\|u\|_{\rm HS}^2$。则在任意量子比特局部维数，

$$
 \nu_+\le12\kappa .
 \tag{1}
$$

若概率为 $(1,r,r,a,b,c,c)$、$1\ge r\ge a\ge b\ge c>0$，记 $h=1-r,\ q=r-a,\ g=hq$。完整反对易缺陷满足

$$
 2J(C,C)\ge g^2\kappa,\qquad C=N^2.
 \tag{2}
$$

这里 $q$ 是概率间隙。本文中归一化物理投影参数 $4/d$ 另写作 $q_F$。式 (1)、(2) 与末节的加权 packing 界合并，得到这一族的全轨道比较。

## 只计四个外部颜色

沿用[固定四点仿射支撑的二楔估计](rank7_124_small_defect_closure.md)的记号。$D$ 是四点仿射稳定子块，$Y$ 是固定的五维空间，$\Omega$ 是其单位体积元。$L_\Omega$ 在二形式上定义为基准 $2I$ 减去测试 $\Omega$ 时的归一化五点算子。它满足 $-I/2\preceq L_\Omega\preceq2I$，且 $\|L_\Omega-3I/4\|\le5/4$。对任意单位可分解二楔 $\alpha$，按其平面与 $D$ 的主角分解

$$
 \alpha=c_0\alpha_0+\eta_1+\eta_2+\zeta,\qquad
 \|\eta_1\|^2+\|\eta_2\|^2\le E,\qquad
 \|\zeta\|\le E/2,\qquad E=\operatorname{Tr}P_{\mathrm{plane}(\alpha)}(I-P_D)\le2.
$$

其中 $c_0\ge0$，$\alpha_0$ 的两腿都在 $D$，每个 $\eta_i$ 含一条支撑内参考腿及一条外部腿，$\zeta$ 两腿均在外部。这四项正交。将坐标按与 $D$ 平行的四点块赋颜色，把 $D$ 的颜色记作 $0$。将 $\eta_i=\sum_{b\ne0}\eta_{ib}$ 按其外腿颜色分解。

在交叉项 $\langle\alpha_0,L_\Omega\eta_{ib}\rangle$ 的匹配方向中，归一化稳定子四形式的参考侧和变分侧两次收缩分别留下颜色 $(b,b)$、$(0,b)$ 的两条尾腿。理由是参考侧两根输入都在零色，使方向的商像秩至多一；变分侧的 $0,b$ 输入又迫使商像为 $\{0,b\}$。有贡献的平面两色各占两点。对五粒子提升，其他三个旁观粒子不变。因此交叉项在输入、输出两侧都可以投影到

$$
 R_b=\mathbf1_{\{n_b\ge1,\ n_0+n_b\ge2\}},
$$

其中 $n_j$ 为该颜色的占据数。相应地可将 $\Omega$ 在该交叉项内换成 $\Omega_b=R_b\Omega$。五粒子扇区上有 $\sum_{b\ne0}R_b\preceq4I$。若 $n_0\ge1$，最多有四种外色被占据；若 $n_0=0$，合格颜色至少占两根，最多两种。

取 $\delta=\langle\alpha_0,L_\Omega\alpha_0\rangle$。令 $D_0=2I-A(\alpha_0)$ 为这两条参考腿的五粒子缺陷算子，$D_0\succeq0$，与各颜色占据投影对易。对每个 $\Xi$，$L_\Xi$ 在 $\operatorname{span}(\alpha_0,\eta_{ib})$ 上半正定，因为其二楔有共同腿且支撑在 $0,b$ 两色构成的八点仿射空间。Cauchy–Schwarz 给

$$
 |\langle\alpha_0,L_\Omega\eta_{ib}\rangle|
 \le \sqrt2\,\|\eta_{ib}\|\|\Omega_b\|\,
                 \sqrt{\langle\Omega_b,D_0\Omega_b\rangle}.
$$

用 $\|\Omega_b\|\le1$ 和 $\sum_b\langle\Omega_b,D_0\Omega_b\rangle\le4\delta$，先对颜色、再对两条腿求和，得

$$
 |\langle\alpha_0,L_\Omega(\eta_1+\eta_2)\rangle|
 \le\sqrt{8\delta}\,(\|\eta_1\|+\|\eta_2\|)\le4\sqrt{E\delta}.
$$

因此 $c_0^2\delta$ 与这两个交叉项之和至少为 $-16E$。$\eta_1+\eta_2$ 的对角项至少为 $-E/2$。含 $\zeta$ 的交叉项因其与其余项正交，使用中心化算子，至少为 $-5E/4$；其自身项至少为 $-E^2/8\ge-E/4$。合并即得固定支撑的改进

$$
 L_{ij}-2\le18\,\operatorname{Tr}P_{\operatorname{span}(x_i,x_j)}(I-P_D).
 \tag{3}
$$

## 小、中、大缺口

当 $\kappa\ge1/24$，通用 packing 的 $\nu\le1/2$ 立即给式 (1)。当 $\kappa=0$，由[零缺口的物理刚性](rank7_three_level_124_overlap.md)有 $\nu\le0$。以下取 $0<\kappa\le1/24$。沿用[扩展至 $1/20$ 的傅里叶舍入](rank7_four_level_1231_packing.md)及[其原始恒等式](rank7_shared_anchor_fourier_rounding.md)，存在相异平行二维稳定子码 $Q,Q'$，令 $e=2-\operatorname{Tr}(P_MQ')$、$f=1-\langle x_0,Qx_0\rangle$、$E=e+2f$，则

$$
 E<1/5,\qquad 5\kappa\ge2E(1-E)^2 .
$$

$2E(1-E)^2$ 在 $[0,1/5]$ 递增，且 $2(1/7)(6/7)^2=72/343>5/24$，故 $E<1/7$。令 $D=Q+Q'$，记 $f_o,e_o$ 为首腿、两根中间腿分别漏出整个 $D$ 的平方质量，并置 $E_o=2f_o+e_o\le E$。成对 Pauli 标签的漏质量 $\ell$ 满足

$$
 \kappa\ge2(1-\tau)\ell,\quad
 \tau=(\sqrt e+\sqrt f)^2\le3E/2<3/14,\qquad
 \ell\ge E_o-2f_o e_o\ge(1-E_o/4)E_o\ge(27/28)E_o .
$$

倒数第二个不等式是 $(2f_o)e_o\le E_o^2/4$。故 $\kappa\ge(297/196)E_o$。分别用式 (3) 支付 $L_{01},L_{02}$，得

$$
 \nu\le18E_o\le(3528/297)\kappa<12\kappa .
$$

若只需单独任一对的正超额，同样的常数也够用：小缺口时此对单独的外部漏质量不超过 $E_o$，大缺口时其普适正超额至多 $1/3$。

## 双对角 Pauli 槽共同提高常数

在双拷贝 Hilbert–Schmidt 空间上，令 $\mathcal A$ 为实线性投影，在 Hermitian Pauli 展开中只保留有序反对易标签，令 $S$ 为拷贝交换。定义

$$
 A=\mathcal A(P_0\otimes P_3),\qquad B=SAS=\mathcal A(P_3\otimes P_0),
 \quad J_{ij}=J(P_i,P_j),\qquad K=\langle A,B\rangle_{\rm HS}.
$$

$A+B$ 与 $S$ 对易。由原混合投影和 Pauli 展开的极化，$u=(A+B)|_{\Lambda^2}$，因为 $(P_0\otimes P_3+P_3\otimes P_0)|_{\Lambda^2}$ 正好是 $x_0\wedge M$ 的正交投影。因此

$$
 \kappa=2\|u\|_{\rm HS}^2\le2\|A+B\|_{\rm HS}^2=4(J_{03}+K).
$$

若 $r_v=\operatorname{Tr}(P_0W_v)$、$p_v=\operatorname{Tr}(P_3W_v)$，则 $K=d^{-2}\sum_{[v,w]=1}r_vp_w p_vr_w$。在同一个有序反对易边集上把两因子重新分组为 $r_vr_w$ 和 $p_vp_w$，得 $|K|\le\sqrt{J_{00}J_{33}}$。对两个谱切割使用交换子平方逐矩阵元界，并对 $J$ 的两个槽先后应用，得到

$$
 J(C,C)\ge h^4J_{00}+q^4J_{33}+2g^2J_{03}
 \ge 2g^2(J_{03}+|K|).
$$

两个自槽为非负，几何平均恰为 $g^2\sqrt{J_{00}J_{33}}$。和前式合并即为式 (2)。此支付与 $24\|L_-(C)\|_{\rm HS}^2$ 在原缺陷分解中是两项，可以同时使用。[Pauli 槽、极化及缺陷分解](rank7_two_level_defect_transport.md) · [共享首腿投影的交换子表示](rank7_three_level_124_conditional_matching.md)

## 与等底两腿的加权证书对接

假设固定标架的加权外积证书给非负量 $B_*$，使

$$
 \mathcal E\le c^2 H_0\nu-\tfrac12g B_*,
 \qquad W-W_{\rm CB}=c^2\nu-B_*,
 \qquad H_0=g-c(h+3q)-\tfrac52c^2 .
$$

$\mathcal E=(c_F-c_{F,\rm CB})/q_F$。若 $\nu\le0$，等中间两根的正向证书已经给出比较。以下取 $\nu>0$；若 $H_0\le0$，上述 $\mathcal E\le0$ 足够。因两条末腿相等，[两个投影的条件匹配式 (3)](rank7_general_two_probe_matching.md) 对共享探针给 $2\langle u,L_-\rangle\ge g\kappa+c^2\nu-B_*$。混合与反对易缺陷至少为

$$
 12(g\kappa+c^2\nu-B_*)_+^2/\kappa+g^2\kappa.
$$

设 $G=g/c^2,\ z=\kappa/\nu\ge1/12,\ t=B_* /(c^2\nu)\ge0$。$H_0>0$ 和 $h+3q\ge2\sqrt{3g}$ 给 $G-2\sqrt{3G}-5/2>0$，从而 $G>16$（左边在 $[0,16]$ 的两端及其间均为负）。将支付和 packing 中的负 $B_*$ 项除以 $c^4\nu$，需与 $168(G-2\sqrt{3G}-5/2)$ 比较。支付侧至少为

$$
 12(Gz+1-t)_+^2/z+G^2z+84Gt .
$$

这个关于 $t\ge0$ 的凸函数在零点右导数为 $60G-24/z>0$，故取 $t=0$ 为下界。所得 $13G^2z+24G+12/z$ 在 $z\ge1/12$ 严格递增，因为 $13G^2-12/z^2>0$。取 $z=1/12$，支付减所需增益的差乘 $4/3$，置 $x=\sqrt{G/3}$，即得

$$
 13x^4-576x^2+1344x+752 .
$$

写 $y=x-4>-2$，此式等于 $[13(y+8)^2-160]y^2+64y+240\ge308y^2+64y+240>0$。因此在该加权外积证书的整个适用范围，式 (1)、(2) 足以支付全部正重叠超额。本段不使用四楔压缩间隙。
