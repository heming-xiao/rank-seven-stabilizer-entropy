# 共享首腿 1+2+4 缺口的 Pauli 傅里叶舍入

2026-11-17。设 $d=2^n\ge8$，$\rho=|x\rangle\langle x|$，$P=P_M$ 是 $x^\perp$ 中的秩二投影。设 $p_a=\|PW_a\bar x\|^2$，$a$ 遍历斜 Pauli 标签，$m=d/2$，$\kappa=m^{-1}\sum_a p_a(1-p_a)$。下文直接从 $\kappa$ 得到同一组稳定子生成元的两个不同二维字符空间 $Q,Q'$（也用同字母表示投影）。在整个 $0\le\kappa<1/32$ 内，

$$
 e_M=2-\operatorname{Tr}PQ'\le10\kappa,\qquad
 e_x=1-\langle x,Qx\rangle\le
 \frac{5\kappa}{2(1-10\kappa)^2}\le\frac{640}{121}\kappa.
 \tag{1}
$$

因此两码漏质量和至多 $(10+640/121)\kappa$，常数和区间均与环境维数无关。再保留对 $D$ 的两组不同标签贡献，得到更强的 $e_M+2e_x<1/10$，并证明舍入两码并集的外部加权漏质量至多 $100\kappa/153$。结合固定四点支撑的五点估计 $22$，共享首腿的超额 $\nu=L_{01}+L_{02}-4$ 满足 $\nu_+\le(2200/153)\kappa<16\kappa$（$\kappa>0$），足以支付原三层谱的缺陷。末尾也保留了首腿精确在舍入码 $Q$ 时的较小常数。

## 混合缺口的实傅里叶表达式

用 Hermitian Pauli $W_v$，记 $\eta_v=(-1)^{q(v)}$ 为转置奇偶性，$\chi_v(a)=(-1)^{[a,v]}$ 为辛字符。对全部 Pauli 标签定义

$$
 r_v=\operatorname{Tr}(\rho W_v),\quad u_v=\operatorname{Tr}(P W_v),
 \quad b_v=\|P W_vx\|^2,\quad
 D=d^{-1}\sum_v u_v^2(1-r_v^2),\quad C=d^{-1}\sum_v r_vu_v b_v .
$$

则有精确恒等式

$$
 \kappa=D+C,\qquad
 D=d^{-1}\sum_v r_v^2\big[2-\operatorname{Tr}(PW_vPW_v)\big]
    =2J(P,\rho).
 \tag{2}
$$

为证第一式，把 $p_a=\operatorname{Tr}(P W_a\bar\rho W_a)$ 延拓到全部标签。Pauli 展开得 $p_a=d^{-1}\sum_v \eta_v\chi_v(a)r_vu_v$。字符 Parseval 给 $\sum_a p_a^2=\sum_v r_v^2u_v^2$，而 $\sum_v u_v^2=2d$。又有 $d^{-1}\sum_a\eta_a\chi_v(a)p_a=\eta_v b_v$。例如用二元二次 Gauss 和 $\sum_a\eta_a\chi_w(a)=d\eta_w$，代入上式，得到 $\eta_v d^{-1}\sum_w \chi_v(w)r_wu_w=\eta_v b_v$。因而 $\sum_a\eta_a p_a^2=\sum_v r_vu_v b_v$。斜标签的指示函数是 $(1-\eta_a)/2$，而 $\sum_{a\ {\rm odd}}p_a/m=2$，合并即得。第二式可由对称反对易双槽量的交换子表示推出，或直接把 $\operatorname{Tr}(P W_vP W_v)$ 展为 $d^{-1}\sum_w\chi_v(w)u_w^2$，并用 $d^{-1}\sum_v\chi_v(w)r_v^2=\operatorname{Tr}(\rho W_w\rho W_w)=r_w^2$。[双槽量及交换子表示](rank7_two_level_defect_transport.md)

## 奇维压缩使负交叉项至多吃掉五分之四

有全域不等式 $C\ge-4D/5$，从而

$$
 D\le5\kappa .
 \tag{3}
$$

只需考察 $r_vu_v<0$ 的标签。在本段固定 $W=W_v$，写 $r=|r_v|$、$u=|u_v|$、$b=b_v$。令

$$
 a=1-r^2-b,\qquad
 l=2-\operatorname{Tr}(PWPW)-b.
$$

两者非负，分别是 $Wx$、$W$ 作用于 $M$ 的两根标准正交基后，漏出三空间 $T=\mathbb Cx+M$ 的平方质量。在 $T$ 上压缩 $W$ 得三维 Hermitian 收缩 $H$，满足 $\operatorname{Tr}(I-H^2)=a+l$ 且 $|\operatorname{Tr}H|=|u-r|$。对 $|\operatorname{Tr}H|\le1$，固定迹时三个位于 $[-1,1]$ 的本征值平方和最大为 $2+|\operatorname{Tr}H|^2$。这是凸函数在固定和盒截面上于极点取最大，极点可取 $(1,-1,\operatorname{Tr}H)$。故

$$
 a+l\ge [\,1-(u-r)^2\,]_+ .
$$

若 $u\le2r$，则 $|u-r|\le r\le1$，所以 $a+l\ge1-r^2\ge b$。记 $D_v=u^2(b+a)+r^2(b+l)$，即式 (2) 两种求和的两个对应项之和。于是 $D_v\ge b[u^2+r^2+\min(u^2,r^2)]$，而 $2ur/[u^2+r^2+\min(u^2,r^2)]\le1/\sqrt2$。若 $u\ge2r$，仅用 $D_v\ge b(u^2+r^2)$，便有 $2ur/(u^2+r^2)\le4/5$。所以在两种情形均有 $2urb\le(4/5)D_v$。非负交叉标签无需估计；加总并用 $\sum_vD_v=2dD$ 就得式 (3)。

## 从交换群直接定位两码

取所有满足 $r_v^2>1/2$ 的标签。它们两两对易，因为反对易的两个 Hermitian Pauli 对纯态 $\rho$ 的期望平方和至多一。扩为最大对易群 $G$。在群外 $1-r_v^2\ge1/2$，由 Pauli Parseval 及式 (3)，

$$
 \|P-\mathcal E_G P\|_{\rm HS}^2=d^{-1}\sum_{v\notin G}u_v^2
 \le2D\le10\kappa .
$$

在 $G$ 的稳定子基中取 $P$ 的两个最大对角元之和所对应的坐标投影 $Q'$。若 $g_i$ 表示全部对角元，$0\le g_i\le1,\sum g_i=2$，则前两项和至少为 $\sum_i g_i^2$。故 $e_M\le\|P-\mathcal E_G P\|_{\rm HS}^2$。两条不同的 $G$ 字符在指数二的子群 $H_0$ 上相同，$Q'$ 恰为其二维字符块。

每个 $h\in H_0$ 在 $Q'$ 上为同一符号（依赖于 $h$），在补空间上至多损失 $e_M$ 的迹。因此 $|u_h|\ge2(1-e_M)$。记 $p_\lambda=\|Q_\lambda x\|^2$ 为 $H_0$ 的各字符概率。$|H_0|=d/2$，群内的字符 Parseval 得

$$
 D\ge2(1-e_M)^2(1-\sum_\lambda p_\lambda^2).
$$

取概率最大的字符块为 $Q$，则 $e_x\le1-\sum p_\lambda^2$，式 (1) 随即成立。最后，若 $Q=Q'$，则由 $\rho+P$ 是秩三正交投影，有 $3-e_x-e_M=\operatorname{Tr}[(\rho+P)Q]\le2$。而在 $\kappa<1/32$，式 (1) 给 $e_x+e_M<(10+640/121)/32<1$，矛盾。故两码相异且平行。

## 两个互不相交的 Pauli 区域给出第二次舍入

以下记 $e=e_M,\ f=e_x,\ E=e+2f$。在式 (2) 对 $D$ 的第一个表示中保留码稳定子 $H_0$ 和其辛中心化子 $H_0^\perp$ **之外**的标签。由前节，$H_0$ 部分至少为 $2(1-e)^2(1-\sum_\lambda p_\lambda^2)$。取最大字符概率为 $1-f$，其余之和为 $f$，因此该项至少是 $4(1-e)^2f(1-f)$。

若 $v\notin H_0^\perp$，则 $W_vQ$ 与 $Q$ 正交，故 $W_vx$ 在 $Q$ 的投影平方范数至多 $f$。用投影测量 $\{Q,I-Q\}$ 对两向量分块取 Cauchy–Schwarz，因 $f<1/2$ 得 $|r_v|\le2\sqrt{f(1-f)}$。具体地，测试 $W_vx$ 在 $Q$ 的概率 $p\le f$ 时，上界 $\sqrt{(1-f)p}+\sqrt{f(1-p)}$ 在这一区间递增。该集合上的 $d^{-1}\sum u_v^2$ 恰为 $P$ 的不同 $H_0$ 字符块间的 Hilbert–Schmidt 平方和；保留 $Q'$ 与其补空间之间的两个非对角块，至少为 $2\operatorname{Tr}[Q'P(I-Q')P]$。将 $B=Q'PQ'|_{Q'}$ 代入，得到

$$
 2\operatorname{Tr}B(I-B)
 =2[e-\operatorname{Tr}(I-B)^2]\ge2e(1-e).
$$

两个不交区域的贡献相加，给出

$$
 5\kappa\ \ge D\ \ge 2e(1-e)(1-2f)^2+
              4(1-e)^2 f(1-f)\ \ge 2E(1-E)^2 .
 \tag{4}
$$

最后用 $E<1$ 及 $(1-e)(1-2f)\ge1-E$；第二项同理有 $(1-e)\sqrt{1-f}\ge1-E$。粗界 (1) 已保证 $E<5/16+40/121=1245/1936$。在区间 $[1/10,1245/1936]$ 上，$2E(1-E)^2$ 的最小值取于端点（中间仅在 $1/3$ 有极大）。两个端点值减去 $5/32$ 分别为 $23/4000$ 和 $27564325/3628156928$，均为正。结合式 (4) 与 $\kappa<1/32$，得到 **$E<1/10$**。

## 两码并集的外部漏质量

Clifford 化后令两码的坐标颜色为 $0,c$。每种颜色是平行二点坐标块。记 $\mathcal A$ 为把 $\bar Q$ 送到 $Q'$ 的斜 Pauli 标签集（坐标表象中 $\bar Q=Q$）。其大小为 $d$，因为可行平移恰有两个，每个允许 $d/2$ 个斜相位字符。置 $\ell=m^{-1}\sum_{a\in\mathcal A}(1-p_a)$，相同的 $\ell$ 也等于 $\mathcal A$ 外部斜标签上的 $m^{-1}\sum p_a$。

若 $a\in\mathcal A$，则 $J_ax$ 在 $Q'$ 上的质量为 $1-f$。$P$ 与 $Q'$ 的最大主角正弦不超过 $\sqrt e$。分解 $J_ax$ 在 $Q'$ 内外的分量，可得 $\| (I-P)J_ax\|\le \sqrt e+\sqrt f$。若 $a\notin\mathcal A$，则 $J_ax$ 在 $Q'$ 上的质量至多 $f$，同理 $\|P J_ax\|\le\sqrt e+\sqrt f$。因此以 $\delta=(\sqrt e+\sqrt f)^2\le(3/2)E<3/20$ 统一控制内侧 $1-p_a$ 及外侧 $p_a$，得到

$$
 \kappa\ge 2(1-\delta)\ell .
$$

再置 $D_0=Q+Q'$，$f_o=\|(I-D_0)x\|^2$，$e_o=\operatorname{Tr}P(I-D_0)$。$\ell$ 是两条二楔 $x\wedge y_i$（$y_1,y_2$ 为 $M$ 的标准正交基）在归一化斜 Pauli 二形式基中，标签不属于 $\mathcal A$ 的总平方质量。这因为每个二形式基坐标平方模恰为相应行的 $|\langle y_i,J_a x\rangle|^2/m$。$\mathcal A$ 的每个二形式只连接颜色 $b$ 与 $b+c$；其坐标边不会跨越 $D_0$ 与 $D_0^\perp$。因此 $\ell$ 至少为每个二楔在 $D_0\wedge D_0^\perp$ 的平方质量之和。

对一条 $y_i$，这份质量恰是张量 $(D_0x)\otimes((I-D_0)y_i)-(D_0y_i)\otimes((I-D_0)x)$ 的平方范数。由 $x\perp y_i$，其交叉项为非负的 $2|\langle (I-D_0)x,(I-D_0)y_i\rangle|^2$。故

$$
 \ell\ge(1-f_o)e_o+f_o(2-e_o)
 \ge(1-2f_o)(2f_o+e_o).
$$

现在 $f_o\le f<E/2<1/20$。两式合并得

$$
 \boxed{\quad \kappa\ge (153/100)(2f_o+e_o).\quad}
 \tag{5}
$$

若采用固定四点仿射支撑 $D_0$ 的五点估计 $L_X-2\le22\operatorname{Tr}[P_X(I-D_0)]$，分别取 $X=\operatorname{span}(x,y_i)$ 并相加，式 (5) 即给 $\nu_+\le(2200/153)\kappa$，严格优于待证支付常数 16。$\kappa\ge1/32$ 时原有 packing 的 $\nu\le1/2$ 已足够，故合起来覆盖所有 $\kappa$。该五点估计的关键步骤是：将双收缩的参考两腿投在 $D_0$ 中，对一条偏离单色 $b$ 的腿，双线性交叉项在输入和输出端都需至少一个颜色 $b$ 粒子。参考五粒子算子与各颜色占据对易，按占据投影至多计五次求和，再对合成的缺陷交叉项配方。所需的双腿八点仿射支撑算子界对任意五形式成立。详细的固定二楔证明由主稿单列。[已证八点算子界](reviews/rank7_two_link_independent_review.md) · [谱的标量支付接口](rank7_three_level_124_conditional_matching.md)

## 首腿精确在舍入码中的几何子情形

设 $x\in Q$，令 $\mathcal A$ 为将 $\bar Q$ 送到 $Q'$ 的斜 Pauli 标签。Clifford 化可使两码成为同一线性二点方向的两个坐标陪集；斜 Pauli 框架作为反酉族在 Clifford 化下仅作带相位置换（$W\mapsto U W U^{\mathsf T}$，由 Clifford 的 $U U^{\mathsf T}$ 为 Pauli 直到相位，以及转置斜性不变）。在坐标表象中两个不同的平移差把 $Q$ 的两标签送入 $Q'$，每个差恰有 $d/2$ 个斜标签，故 $|\mathcal A|=d$。$J_a x$ 在 $\mathcal A$ 内属于 $Q'$，在外则与 $Q'$ 正交。完整斜紧框架 $m^{-1}\sum_{a\ {\rm odd}}|J_a x\rangle\langle J_a x|=I-\rho$ 压到 $Q'$ 后可得

$$
 m^{-1}\sum_{a\in\mathcal A}(1-p_a)=
 m^{-1}\sum_{a\notin\mathcal A,\ a\ {\rm odd}}p_a=e_M .
$$

内侧逐点 $p_a\ge1-e_M$，外侧 $p_a\le e_M$，因为相应正算子压缩的迹亏损或迹分别为 $e_M$。所以 $\kappa\ge2e_M(1-e_M)$。

固定 $M$ 中一根单位向量 $y$ 并记 $Y$ 为除 $x,y$ 外的五根尾帧的空间。在 $x^\perp$ 定义 Hermitian 型 $D_Y(z)=2\|z\|^2-q^{-1}\sum_{i<j}\|\Pi_F(x\wedge z\wedge u_i\wedge u_j)\|^2$。Theorem 17 的完整补全给 $-\tfrac12I\preceq D_Y\preceq2I$。仿射八点和相反 Pauli 谱扇区的五形式算子界保证：$D_Y$ 在 $(Q+Q')\cap x^\perp$ 上压缩半正定；也在任何与 $Q$ 取相反 Pauli 字符、且包含 $Q'$ 的半空间上压缩半正定。这里允许固定的 $Y$ 不与测试对完全正交，将其五形式按测试二平面的占据数 $0,1,2$ 分成剩余五、四、三粒子扇区即可。[已核算子界和非正交测试](rank7_joint_gram_astra.md) · [八点和相反 Pauli 扇区](reviews/rank7_two_link_independent_review.md)

写 $y=\xi+\eta$，$\xi=Q'y$，$h=\langle\xi,D_Y\xi\rangle\ge0$；另写 $\eta=\eta_0+\eta_e$，其中 $\eta_0\in Q$，$\eta_e\perp Q+Q'$。在标签商空间上把 $Q,Q'$ 的颜色分别记为 $0,c$。均匀取满足 $\ell(c)=1$ 的二元线性字符。所有外部颜色有一半机会取值 1，故 $\eta_e=2\mathbb E_\ell P_{\ell=1}\eta_e$。半正定压缩 Cauchy–Schwarz 和 $\|D_Y\|\le2$ 给

$$
 |\langle\xi,D_Y\eta\rangle|\le
 \sqrt{2h}\,(\|\eta_0\|+\sqrt2\|\eta_e\|)\le\sqrt{6h}\,\|\eta\|.
$$

因此 $L_{xy}-2=-\langle y,D_Yy\rangle\le-h+2\sqrt{6h}\|\eta\|+\|\eta\|^2/2\le(13/2)\|\eta\|^2$。对两条中间腿加总得

$$
 \nu_+\le(13/2)e_M\le \frac{13}{4(1-e_M)}\kappa
 \le\frac{52}{11}\kappa <5\kappa\qquad(0<\kappa<1/32).
$$

最后一步用 $e_M<5/16$；$\kappa=0$ 由前式直接给 $\nu_+=0$。若改为 $M$ 精确等于某秩二稳定子编码，选择该编码的两条稳定子基作中间两腿，分别用稳定子锚点界也得 $\nu\le0$，对 $x$ 无额外限制。中间基的这种选择不改变两个占据的和。

