# 主峰分裂后的同时支付：混合探针平移与保留的反对易项

2026-11-18。采用七个排序正概率 $(\alpha,\beta,\gamma,a,b,c,d)$，以及

$$
 h=\alpha-\beta,\quad k=\beta-\gamma,\quad q=\gamma-a,\quad
 g=hq,\quad m=h+k+q=\alpha-a,\quad \Delta=km,\quad
 R=k^2[k^2+(h^2+q^2)/2].
$$

这里 $d$ 是最小概率，物理维数另记 $D$。本报告给出直接复用“第二、第三概率相等”证明的联合标量条件。用最高对的附加加权 packing 定价，所得充分条件为

$$
 \boxed{\quad
 \frac{12\Delta^2+R}{4}+\frac{g^2}{24}
 \ \ge\ 144d^2\Delta-168k b c d .
 \quad} \tag{1}
$$

若只使用最高对基本价格 $\mathcal E-\mathcal E_0\le\Delta U_1$，仍可用较强的充分条件将式 (1) 右侧替换为 $144d^2\Delta$。这两个条件允许七个概率全部不同，且对任意量子比特二分割给出排序计算基的纯度比较。它们是充分条件。

## 利用交叉 Gram 的符号平移

记 $u,u_1$ 为共享及单独最高对混合探针，$L=L_-(C)$，$2\|u\|^2=\kappa$，$2\|u_1\|^2=\kappa_1$，$2\langle u,u_1\rangle=c_1\ge0$。由[条件匹配和 Gram 恒等式](rank7_general_two_probe_matching.md)，

$$
 2\langle u,L\rangle\ge H_s+\Delta c_1,\qquad
 2\langle u_1,L\rangle\ge \Delta\kappa_1+U_1,
 \qquad U_1=d^2v_1-B_1,\ B_1\ge0.
$$

这里 $v_1=L_{01}-2$，$\nu=L_{01}+L_{02}-4$。$H_s$ 是等中间谱证明所采用的共享极化下界，但其加权外积必须使用**实际**谱：在该证明记号下
$H_s=G\kappa+cd\,\nu-B$，其中 $G=g-\lambda(b^2-cd)$、$B=B_0+kD_A$；$B_0$ 为对应基谱的损失，$D_A=a-\sum_{j=3}^6t_j w_{012j}\ge0$。$\lambda=2$ 或 $200/11$ 由同一标架的 $\kappa$ 决定。

对任何 $s\ge0$ 取 Hilbert–Schmidt 平方 $\|L-su-\Delta u_1\|^2\ge0$，交叉的 $\Delta c_1$ 精确消去，得到

$$
 24\|L\|^2\ge 24sH_s-12s^2\kappa
       +12\Delta^2\kappa_1+24\Delta U_1 .
$$

所以可将首两项对 $s\ge0$ 优化，保留原先的全部共享探针支付 $12(H_s)_+^2/\kappa$，此外仍有明确的最高对支付。若 $\kappa=0$，直接取 $s=0$ 即可。此处不把同一个范数的两个独立 Cauchy–Schwarz 下界相加。

## 共享标量只需一半反对易项

[一般前三谱隙的双槽估计](rank7_two_probe_anticommuting.md)给 $2J(C,C)\ge g^2\kappa+R\kappa_1$。在[等中间谱证明](rank7_equal_middle.md)的正共享增益分支，可以一直只用其中 $g^2\kappa/2$ 配合完整的共享混合项；剩下的 $g^2\kappa/2$ 可用于其他增益。大缺口 $\kappa\ge11/200$ 的原证明已只用了这一半。

小缺口原标量的唯一改动是把 $g^2/12$ 换为 $g^2/24$。正共享增益迫使 $g>16b^2$，因此在 $0<S=cd\le b^2$ 上，

$$
 [(g-2b^2+14S)^2+g^2/24]/S
$$

仍为递减函数，其导数为 $196-[(g-2b^2)^2+g^2/24]/S^2<0$。原先对亏量和 $\kappa/\nu$ 的单调性在减少反对易项后同样成立，因为共享混合项本身已在相应区间递增。取 $S=b^2$、归一化 $G_0=g/b^2$，需证明

$$
 (G_0+12)^2+G_0^2/24>
 168(G_0-2\sqrt{3G_0}-5/2).
$$

令 $x=\sqrt{G_0/3}$，$y=x-4>-2$。两边差乘 $4/3$ 恰为

$$
 \tfrac{25}{2}x^4-576x^2+1344x+752
 =[\tfrac{25}{2}(y+8)^2-176]y^2-64y+112
 \ \ge\ 274y^2-64y+112>0 .
$$

原基谱为 $(\alpha-k,\gamma,\gamma,a,b,c,d)$，不是假设概率已归一化至一；上述所有原谱比较通过共同缩放仍成立。$h,q$ 在抬升过程中不变。

## 支付实际最高对增益

在同一物理标架上，使用下列最高对价格，其中 $P=0$ 对应基本版本，$P=k b c d$ 对应附加五单项式版本：

$$
 \mathcal E-\mathcal E_0\le\Delta U_1-Pv_1
 \quad\text{在 }v_1>0\text{ 时},\qquad
 \mathcal E-\mathcal E_0\le\Delta U_1\quad\text{总成立}.
 \tag{2}
$$

这里 $\mathcal E$ 为除以 $q_F=4/D$ 的线性外积重叠增益。完整的最高对亏量证明见[抬升后的最高对价格](rank7_highest_pair_split_loss.md)。已证 $B_1\ge qD_A$，故若 $\nu>0$，把式 (2) 和基谱 packing 相加后，

$$
 \mathcal E\le cd H\nu-\tfrac g2 B
       +d^2\Delta v_1-(\Delta-kh/2)B_1-P(v_1)_+ ,
 \quad H=g-b(h+3q)-\tfrac52 b^2 .
$$

特别地 $168(\Delta-kh/2)\ge84\Delta\ge24\Delta$。因此可用上述混合平移产生的 $-24\Delta B_1$，其代价由外积剩余负项完全吸收。若 $cd H\nu-gB/2\le0$，共享混合支付取零；若此式为正，则前节的共享标量比较对实际 $B$ 成立。若 $\nu\le0$，基谱的原正向证书已经给 $\mathcal E_0\le0$，可直接用式 (2)，无需引入共享亏量或共享极化。任一分支都留下最高对账目

$$
 (12\Delta^2+R)\kappa_1+g^2\kappa/2
 \ \ge\ (144d^2\Delta-168P)(v_1)_+ .
$$

这是充分要求；若 $v_1\le0$，将正部取零合法，因为其剩余的实际线性价格 $144d^2\Delta$ 非负。由两个物理几何界 $(v_1)_+\le4\kappa_1$、$(v_1)_+\le12\kappa$，式 (1) 恰保证此要求。这样已同时覆盖所有标架的正负超额分支。[最高对几何舍入](rank7_wedge_pauli_rounding.md) · [共享及单独五点的常数 12](rank7_shared_anchor_twelve_and_anticommuting.md) · [亏量 $B_1,D_A$ 与抬升恒等式](rank7_leading_split_packing.md)

两个简明推论只需基本版本 $P=0$。由 $R\ge\Delta^2/5$，若 $\Delta\ge(2880/61)d^2$，式 (1) 的基本版本自动成立。若 $g\ge203d^2$，对任意 $\Delta\ge0$ 也自动成立：二次式 $(61/20)\Delta^2-144d^2\Delta+g^2/24$ 的判别式为负。上述条件本身没有要求其它五条尾概率近似相等。

## 反向交叉价格与可选平移

在一般条件匹配的逐标记估计中，除最高对与次高对的间隙 $\Delta$ 外，次高对与中间对间还保留非负价格 $g(1-p)$。将同一估计乘 $p_1$ 并求和，最高对探针实际上满足

$$
 2\langle u_1,L\rangle\ge\Delta\kappa_1+U_1+g c_1 .
$$

余项为 $j\langle p_1(1-p-p_{12})\rangle+h_{\rm tail}\langle p_1(3-s_6)\rangle\ge0$。这里 $h_{\rm tail}=b(c-d)$，$s_6$ 是六点内部斜匹配量。对两探针以 $s,t\ge0$ 同时作下界，完整的交叉系数因此是 $24(s\Delta+t g-st)c_1$。需要共享支付时 $\nu>0$ 且 $g>16b^2\ge16cd$；优化共享平方所用的 $s=(H_s)_+/\kappa\le g+12cd<2g$。其余分支取 $s=0$ 即可。故对整个 $0\le t\le2\Delta$，交叉系数均非负，原基谱比较全部保留。

取 $t=(1+z)\Delta,\ 0\le z\le1$。此时最高对的混合支付为
$12(1-z^2)\Delta^2\kappa_1+24(1+z)\Delta U_1$。负 $B_1$ 项所需价格仍至多 $48\Delta\le168(\Delta-kh/2)$。于是式 (1) 右侧可以再减去

$$
 \Phi=\max_{0\le z\le1}(24z\Delta d^2-3z^2\Delta^2)
 =\begin{cases}48d^4,&\Delta\ge4d^2,\\
 24\Delta d^2-3\Delta^2,&0\le\Delta\le4d^2.\end{cases}
 \tag{3}
$$

这个改进也适用于 $P=0$ 版本；此时只删去式 (1) 右侧的 $-168k b c d$。若 $v_1\le0$，可直接选 $z=0$，其余论证同前。

## 奇数秩谱支撑的直接舍入

另有一份以 $J_{33}$ 自身控制最高对的几何支付。设 $P_3$ 为前三根的投影，$w_v=\operatorname{Tr}(P_3W_v)$，$\ell_v=3-\operatorname{Tr}(P_3W_vP_3W_v)$。所有 $\ell_v<1/2$ 的标签两两对易，因为任何反对易对的两个奇数秩漏出之和至少为一。将该集扩张为最大对易群 $G$。由 Parseval 和交换子表示，

$$
 \|P_3-\mathcal E_G P_3\|_{\rm HS}^2
 =D^{-1}\sum_{v\notin G} w_v^2
 \le(2/D)\sum_v w_v^2\ell_v=4J_{33}.
$$

在 $G$ 的稳定子字符基中，$P_3$ 的三个最大对角元之和至少为全部对角元的平方和（每项在 $[0,1]$ 且总和三）。因此 $P_3$ 漏出这三条线的总平方质量至多 $4J_{33}$。三条同基坐标总位于一个四点仿射平面内。设 $Q$ 为对应四维稳定子块，由固定块常数 $18$，

$$
 (v_1)_+\le18\operatorname{Tr}[P_{01}(I-Q)]\le72J_{33},\qquad
 \nu_+\le144J_{33}.
$$

这里 $P_{01}$ 是前两根张成的单粒子平面的投影。这个论证不需预设 $J_{33}$ 够小，且不要求 $P_{01}$ 在三根高腿内还有额外 Pauli 对称性。[奇数秩漏出不等式](rank7_two_probe_anticommuting.md) · [固定四点块常数 $18$](rank7_shared_anchor_twelve_and_anticommuting.md)

实际支付的三个共享反对易槽 $2(h^4J_{11}+q^4J_{33}+2g^2J_{13})$ 至少为 $g^2\kappa$。前节的共享比较使用其一半后，剩余的一半既至少为 $g^2\kappa/2$，又至少为 $q^4J_{33}$。于是式 (1) 左侧的 $g^2/24$ 可以加强至 $\max\{g^2/24,q^4/72\}$，并可与式 (3) 同时使用。此处对同一份剩余反对易支付取最大值。

## 单对常数 $5/2$ 和独立的压缩支付

[最高对的自适应舍入](rank7_highest_pair_geometry_five_halves.md)改进了本节所需的单探针常数。令 $K=5/2$，则 $(v_1)_+\le K\kappa_1$。再置

$$
 \sigma=\left(\sqrt{\alpha\beta c d}-\sqrt{\alpha\gamma a b}\right)_+,\qquad
 \Phi_K=\begin{cases}
 12K d^4,& \Delta\ge Kd^2,\\
 24\Delta d^2-(12/K)\Delta^2,&0\le\Delta\le Kd^2 .
 \end{cases}
$$

则本报告的联合充分条件可写为

$$
 \boxed{\quad
 \frac{12\Delta^2+R}{K}
 +\max\{g^2/24,\ q^4/72\}+64\sigma^2+\Phi_K
 \ \ge\ 144d^2\Delta-168k b c d .
 \quad} \tag{4}
$$

为得到 $\Phi_K$，在式 (3) 的平移中置
$z=\min(1,Kd^2/\Delta)$，当 $\Delta=0$ 可取 $z=0$。这是 $24z\Delta d^2-(12/K)z^2\Delta^2$ 在 $[0,1]$ 的最大值。其余被 $\kappa_1$ 支付的系数 $12(1-z^2)\Delta^2+R$ 非负，故代入较强的几何常数有效。

压缩项来自独立的实际四楔压缩缺陷 $\mathcal D_F$，归一化为原比较式中被减去 $96\mathcal D_F$。在前两方向双占的四楔块中，$\Lambda^4\sqrt C$ 的最小特征值为 $\sqrt{\alpha\beta c d}$；块外的最大值为 $\sqrt{\alpha\gamma a b}$。两块正向谱差为 $\sigma$。若 $\sigma>0$，归一化压缩 $T$ 在最高对块上的主块 $T_{01}$ 满足
$\mathcal D_F\ge\sigma^2\operatorname{Tr}T_{01}(I-T_{01})$，其中内部非投影项系数亦至少为 $\sigma^2$。当 $v_1>0$，由 $\operatorname{Tr}T_{01}=2+v_1$、$v_1\le1/3$ 及谱取整即得
$\mathcal D_F\ge\sigma^2v_1(1-v_1)\ge(2/3)\sigma^2 v_1$。当 $\sigma=0$ 或 $v_1\le0$，使用 $\mathcal D_F\ge0$。此前混合、反对易两部分均没有使用该压缩项，故 $64\sigma^2$ 可独立相加。[任意配对的压缩取整及归一化](rank7_compression_slack_astra.md)

例如谱正比于 $(56/5,11/2,5/2,17/10,8/5,11/10,1)$ 时，$g=114/25$，$\Delta=57/2$，$R=46017/200$，$\Phi_K=30$。两块端点的平方分别为 $1694/25$、$1904/25$，故 $\sigma=0$。仅取反对易余项中的 $g^2/24$，式 (4) 左侧扣除 $\Phi_K$ 后为 $9979251/2500$，右侧也扣除 $\Phi_K$ 后为 $79674/25$。严格裕量为 $2011851/2500$。条件齐次，故这一例和它的充足小邻域均给出归一化概率。当式 (4) 失败，它本身不提供结论。
