# 单个最高对的五点超额与斜 Pauli 缺口

2026-11-18。令物理维数为 $D=2^n\ge8$，$m=D/2$。取正交的二平面 $X$ 与五平面 $Y$，$x,y$ 为 $X$ 的一组标准正交基，$\alpha=x\wedge y$。在反对称 Pauli 标签 $b$ 上令 $p_b=|\langle x,J_b y\rangle|^2$，$J_b=W_b\mathrm{conj}$。记 $\langle f\rangle=m^{-1}\sum_b f_b$。有 $0\le p_b\le1$、$\langle p\rangle=1$、$\kappa_1=\langle p(1-p)\rangle$。令 $L_{XY}$ 为归一化五点量，即 $(4/D)^{-1}\sum_{i<j}\|\Pi_F(\alpha\wedge u_i\wedge u_j)\|^2$，$u_i$ 是 $Y$ 的任一标准正交基。则

$$
 \boxed{\ (L_{XY}-2)_+\le\tfrac52\kappa_1.\ } \tag{1}
$$

物理上界 $L_{XY}\le7/3$ 直接覆盖 $\kappa_1\ge2/15$。以下设 $\kappa_1\le2/15$。[物理五点上界](reviews/rank7_two_link_independent_review.md)

## 自适应选取高质量标签

置 $P=\max_b p_b$ 并取达到最大值的 $b_0$。有 $P\ge\langle p^2\rangle=1-\kappa_1\ge13/15$。令

$$
 t=\tfrac12+\sqrt{P(1-P)},\qquad H=\langle p\,\mathbf1_{p>t}\rangle .
$$

因为 $P>(1+1/\sqrt2)/2$，有 $P>t$。取 $\cos^2\theta=P$，则 $t=\cos^2(\pi/4-\theta)$。当 $p_b>t$ 时，二维斜反酉压缩的乘积界给

$$
 \tfrac12|\operatorname{Tr}(P_XW_{b+b_0})|
 \ge\sqrt{Pp_b}-\sqrt{(1-P)(1-p_b)}>1/\sqrt2.
$$

乘积界来自 $J_{b_0},J_b$ 的 $X$ 内压缩均正比于同一斜反酉，余项矩阵范数不超过右侧被减掉的平方根。任一态上两个反对易 Pauli 的期望平方和至多一，故这些差标签两两对易。[乘积界与 Pauli 归一化](rank7_wedge_pauli_rounding.md)

由 $1-\kappa_1=\langle p^2\rangle\le PH+t(1-H)$ 可知 $H>5/8$。确实，写 $z=2P-1$，有

$$
 5P+3t=4+\tfrac12(5z+3\sqrt{1-z^2})
 \le4+\tfrac12\sqrt{34}<104/15\le8(1-\kappa_1).
$$

令 $U$ 为高质量差标签的线性包。其各向同性保证 $q_0(u)+[u,b_0]$ 在 $U$ 上线性，其中 $q_0$ 是决定 Pauli 转置符号的二次型。每个生成元均使它为零，故整个 $b_0+U$ 均为斜标签。最大各向同性空间的每个仿射陪集若全部同号，则必须全部为正号，由全空间 Gauss 和 $+D$ 与其余陪集符号和零可知。所以 $|U|\le D/2=m$。每个标签质量不超过 $1/m$，高集质量 $>5/8$ 强制 $|U|>m/2$，故 $|U|=m$。

$U$ 的共同字符空间是秩二稳定子编码。整个斜陪集的归一框架张成这些码楔线的直和。记 $\rho$ 为单位可分解 $\alpha$ 在该直和上的质量，$a_0$ 为其在单条码楔上的最大重叠模，$e=1-a_0$。有 $\rho\ge H>5/8$。由各码楔振幅绝对值和至多一，得 $a_0\ge\rho$、$\rho\le a_0^2+(1-a_0)^2$，从而 $a_0\ge3/4$。陪集内外四阶矩的精确舍入估计为

$$
 \kappa_1\ge f(a_0),\qquad f(a)=4a^2(1-a)(3a-2).
 \tag{2}
$$

这个估计的前提仅是已有上述秩二陪集和 $a_0\ge3/4$。具体地，陪集内四阶权至多 $a_0^4+(6a_0^2+4a_0e+e^2)(\rho-a_0^2)$，外四阶权至多 $4a_0e(1-\rho)$。两者相加再用 $\rho-a_0^2\le e^2$ 即得式 (2)。[陪集基、内外四阶估计](rank7_wedge_pauli_rounding.md)

在 $[3/4,19/20]$ 上，$f'(a)=4a(-12a^2+15a-4)$ 仅可能由正变负；两端值分别为 $9/64$ 和 $6137/40000$，均大于 $2/15$。因此 $a_0>19/20$，而 $4a_0^2(3a_0-2)\ge6137/2000>3$，故 $\kappa_1\ge3e$。取最大码楔所对应的码投影 $Q$。其与 $X$ 的主角余弦为 $c_0,c_1$，$a_0=c_0c_1$，从而

$$
 \epsilon=1-\tfrac12\operatorname{Tr}(P_XQ)
 =1-\tfrac12(c_0^2+c_1^2)\le e<1/20 .
$$

## 用两组半正定压缩控制交叉项

对固定 $Y$，令 $M_Y$ 为上述五点量在二楔空间上的 Hermitian 算子，$L=2I-M_Y$。单洞恒等式给 $0\preceq M_Y\preceq(5/2)I$。对任何稳定子线 $s$，$L$ 在 $s\wedge\mathbb C^D$ 上的压缩半正定，包含 $s$ 与 $Y$ 有重叠的情形。取秩二稳定子码 $Q$ 的一组稳定子正交基 $s_0,s_1$，分解

$$
 \alpha=c\alpha_0+\eta_0+\eta_1+\zeta,\qquad
 \alpha_0=s_0\wedge s_1,\quad \eta_i\in s_i\wedge Q^\perp,\quad
 \zeta\in\Lambda^2 Q^\perp .
$$

这四项正交。两个主角给 $\|\eta_0\|^2+\|\eta_1\|^2\le2\epsilon$、$\|\zeta\|\le\epsilon$。以下写 $L[z]=\langle z,Lz\rangle$，置 $A=|c|\sqrt{L[\alpha_0]}$、$b_i=\sqrt{L[\eta_i]}$。利用 $\alpha_0$ 与 $\eta_i$ 有共同的稳定子锚点，可得除 $\eta_0,\eta_1$ 的相互交叉外，前三项合计至少
$A^2+b_0^2+b_1^2-2A(b_0+b_1)\ge-2b_0b_1$。[单洞界、锚点压缩及主角分解](rank7_rank2_stability_route.md)

另利用 $2I-L=M_Y\succeq0$ 和 $\eta_0\perp\eta_1$，有

$$
 |\langle\eta_0,L\eta_1\rangle|
 \le\sqrt{(2\|\eta_0\|^2-b_0^2)(2\|\eta_1\|^2-b_1^2)}.
$$

对两个二维实向量 $(b_i,\sqrt{2\|\eta_i\|^2-b_i^2})$ 作 Cauchy–Schwarz，得 $b_0b_1+|\langle\eta_0,L\eta_1\rangle|\le2\|\eta_0\|\|\eta_1\|$。故前三项总体期望至少 $-4\|\eta_0\|\|\eta_1\|\ge-4\epsilon$。

因 $\zeta$ 正交于前三项之和，且该和范数至多一，$\|L-3I/4\|\le5/4$ 给与 $\zeta$ 的交叉下界 $-(5/2)\epsilon$。最后 $L[\zeta]\ge-\epsilon^2/2$。于是

$$
 (L_{XY}-2)_+\le\tfrac{13}{2}\epsilon+\tfrac12\epsilon^2
 \le\tfrac{261}{40}e\le\tfrac{87}{40}\kappa_1
 \qquad(\kappa_1\le2/15).
$$

加上 $\kappa_1\ge2/15$ 的物理上界，得到式 (1)。小缺口分支也可保留 $\kappa_1\ge(6137/2000)e$ 给出的较强常数。

若需要较紧的全域常数，以上阈值也可取 $\kappa_*=(8-\sqrt{34})/16$。此时 $8(1-\kappa_*)=4+\sqrt{34}/2$，故高集质量仍至少为 $5/8$，足以确定同一秩二码。因 $2/15<\kappa_*<9/64<6137/40000$ 且 $1-\kappa_*>(1+1/\sqrt2)/2$，余下的端点、近码推导不变。大缺口取 $1/(3\kappa_*)=8(8+\sqrt{34})/45$；它大于 $87/40$。因此式 (1) 中的 $5/2$ 还可换成该常数，或方便的有理上界 $32/13$。
