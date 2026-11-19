# 任意前三档间隙的两探针反对易支付

2026-11-18。设物理局部维数为 $D=2^n$，排序 Schmidt 概率为 $\alpha\ge\beta\ge\gamma\ge a\ge b\ge c\ge d>0$。以 $P_1,P_2,P_3$ 分别表示谱概率算子 $C$ 最高一、二、三条本征线的投影。设 $u_1=\mathcal B(\Lambda^2P_2)$ 是最高对的混合探针，$u=\mathcal B E_H$ 是共享首腿探针，其中 $E_H$ 投到第零根分别与第一、第二根的两个外二楔上（本征线编号从零起）。定义 $\kappa_1=2\|u_1\|_{\rm HS}^2,\ \kappa=2\|u\|_{\rm HS}^2$。注意 $P_1$ 在本文表示单粒子最高线投影，与二楔探针 $u_1$ 不同。

取三个单粒子谱隙 $h=\alpha-\beta,\ k=\beta-\gamma,\ q=\gamma-a$，令 $g=hq,\ \Delta=k(h+k+q)$。则单一实际反对易缺陷可同时支付

$$
 2J(C,C)\ \ge\
 g^2\kappa+k^2\left(k^2+\frac{h^2+q^2}{2}\right)\kappa_1
 \ \ge\ g^2\kappa+\frac{\Delta^2}{5}\kappa_1 .
 \tag{1}
$$

这两个价格 $g,\Delta$ 分别是[一般排序谱的条件匹配](rank7_general_two_probe_matching.md)中 $M_{02}-M_{12}$ 和 $M_{01}-M_{02}$。式 (1) 与 $24\|L_-(C)\|^2$ 是两个不同实际支付项，因此可和两个极化探针的 Gram 支付并用。

## 奇数秩投影的 Pauli 漏出

对任意秩 $s$ 投影 $S$ 及 Pauli $W$ 写 $\ell_S(W)=s-\operatorname{Tr}(SWSW)$（Hermitian 代表，乘积标签统一选相位）。若 $s$ 为奇数且 $U,V$ 是反对易 Pauli，则

$$
 \ell_S(U)+\ell_S(V)\ge1.
 \tag{2}
$$

证明：以 $I,U,V,UV$ 作均匀共轭平均得 $S'$。该正收缩与 $U,V$ 对易。每个本征空间在 $U,V$ 作用下不变，$V$ 将其中 $U$ 的正本征空间与负本征空间双射，因此 $S'$ 的每个本征值均有偶重数。令每对本征值记一次为 $z_i$，有 $z_i\in[0,1]$ 且 $\sum_i z_i=s/2$。因 $s$ 为奇数，半整数总和使 $\sum_i z_i(1-z_i)\ge1/4$，例如固定总和时把尽可能多的 $z_i$ 移至端点可最小化此和。故 $s-\operatorname{Tr}(S'^2)\ge1/2$。

该平均是 Hilbert–Schmidt 正交投影，因而

$$
 s-\operatorname{Tr}(S'^2)
 =\tfrac14[\ell_S(U)+\ell_S(V)+\ell_S(UV)] .
$$

Pauli 展开直接给 $\ell_S(W)=2D^{-1}\sum_{v:[v,W]=1}\operatorname{Tr}(S W_v)^2$。与 $UV$ 反对易的标签恰是与 $U,V$ 反对易的两个标签集的对称差，所以 $\ell_S(UV)\le\ell_S(U)+\ell_S(V)$，证得式 (2)。单量子比特秩一投影取 $U$ 本征线可达等号。

## 三个切割的实际支付

记 $J_{ij}=J(P_i,P_j)$，其归一是 $J(A,B)=D^{-2}\sum_{[v,w]=1}\operatorname{Tr}(AW_v)^2\operatorname{Tr}(BW_w)^2$，按有序标签对计。对 $p_v=\operatorname{Tr}(P_2W_v)^2$ 有 $\sum_{w:[v,w]=1}p_w=(D/2)\ell_{P_2}(W_v)\le D$。故对 $S=P_3$ 应用式 (2) 得

$$
 \begin{aligned}
 J_{22}
 &\le D^{-2}\sum_{[v,w]=1}p_vp_w
       [\ell_{P_3}(W_v)+\ell_{P_3}(W_w)]\\
 &\le(2/D)\sum_v p_v\ell_{P_3}(W_v)=4J_{23}.
 \end{aligned}
$$

对 $S=P_1$ 也有相同证明，因此 $J_{22}\le4J_{12}$。在全部双拷贝 Pauli 展开中仅保留反对易对的算子记为 $\mathcal A$。$\|\mathcal A(P_2\otimes P_2)\|_{\rm HS}^2=J_{22}$，在反对称子空间的限制等于 $u_1$。所以 $J_{22}\ge\kappa_1/2$、$J_{12},J_{23}\ge\kappa_1/8$。同一推导对任意奇数秩测试投影 $S$ 有 $J(P_2,P_2)\le4J(P_2,S)$。

对每个 $W$，在 $C$ 的本征基上比较谱差平方（实际非负谱间隙之和的平方至少为各自平方和），可得

$$
 \|[C,W]\|_{\rm HS}^2\ge
       h^2\|[P_1,W]\|_{\rm HS}^2+k^2\|[P_2,W]\|_{\rm HS}^2+
       q^2\|[P_3,W]\|_{\rm HS}^2 .
$$

对对称双槽 $J$ 的交换子表示先后应用，从而 $2J(C,C)$ 至少为

$$
 2(h^4J_{11}+q^4J_{33}+2h^2q^2 J_{13})
 +2k^4J_{22}+4h^2k^2J_{12}+4k^2q^2J_{23}.
$$

圆括号的两倍已经由[保留自槽的共享首腿不等式](rank7_shared_anchor_twelve_and_anticommuting.md)证明至少为 $g^2\kappa$。其余三项用上一段的下界相加，便是式 (1) 中的第一界。最后由 Cauchy–Schwarz，

$$
 (h+k+q)^2\le (2+1+2)\big(h^2/2+k^2+q^2/2\big),
$$

乘 $k^2/5$ 便得第二界。

## 使用范围

当 $\beta>\gamma$，式 (1) 和两探针 Gram 分别控制实际反对易缺陷与混合缺陷。将最高两条概率一同抬升的加权误差及其剩余标量步骤见[同一标架的抬升比较](rank7_leading_split_packing.md)。
