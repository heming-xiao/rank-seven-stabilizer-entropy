# 固定二平面有相反的 Pauli 本征值时的五维上界

日期 2026-11-17。设 $d=2^n\ge8$、$q=4/d$。若二平面 $X$ 有两个标准正交向量 $x,y$，分别属于同一个非恒等 Pauli 的两个相反本征空间，则对 $Y\subset X^\perp$ 有

$$
B(X,Y)
=q^{-1}\sum_{u_i,u_j\in{\rm ONB}(Y),\,i<j}
  \|\Pi_F(x\wedge y\wedge u_i\wedge u_j)\|^2
\ \le\ \left\lfloor\frac{\dim Y}{2}\right\rfloor .
$$

此处允许两根本征向量在各自本征空间任意取向。特别地，五维 $Y$ 给出 $B\le2$。该命题覆盖确实不含稳定子态且不能酉 Clifford 变换至八点仿射坐标空间的 $d=16$ 二平面。本文给出其中一族的全角度计算。

## 双收缩的 Walsh 变换

Clifford 对称性允许取 Pauli 为最高位的 $Z$。写 $d=2m$，以 $(b,a)$ 标坐标，其中 $b\in\mathbb F_2$ 为最高位，$a\in\mathbb F_2^{n-1}$，这两个最高位本征空间记为 $H_0,H_1$。可取 $x=\phi_0\in H_0$、$y=\phi_1\in H_1$，其中 $\phi_0,\phi_1$ 是任意单位向量。置 $R_b=H_b\ominus\mathbb C\phi_b$。

对每个平面方向 $L$，$\Pi_F$ 的单位基向量是 $\psi_L=\sqrt q\sum_{F\parallel L}e_F$，每个 $e_F$ 都取升序坐标。若 $L$ 的最高位始终为零，每个 $F$ 在同一 $H_b$，故 $a_ya_x\psi_L=0$。其余方向由以下数据唯一标记。

- $w\ne0$ 是 $L$ 中最高位为零的唯一非零差值。
- $k$ 是 $Q_w=\mathbb F_2^{n-1}/\langle w\rangle$ 的元素，标记 $L$ 中最高位为一的两个点的低位陪集。

对 $p\in Q_w$，令 $\eta_{w,p}$ 为该陪集两低位坐标的升序楔积，并写 $\eta_{w,p}^{(b)}$ 为置于 $H_b$ 的副本。方向 $(w,k)$ 的每个平面是 $p$ 中两点置于 $H_0$，$p+k$ 中两点置于 $H_1$。按最高位分块的全标签排序下，$e_F=\eta_{w,p}^{(0)}\wedge\eta_{w,p+k}^{(1)}$。定义 $v^{(b)}_{w,p}=a_{\phi_b}\eta^{(b)}_{w,p}$，则

$$
q^{-1/2}a_ya_x\psi_{(w,k)}=-\sum_{p\in Q_w}v^{(0)}_{w,p}\wedge v^{(1)}_{w,p+k}.
$$

负号来自第二次收缩越过剩余的一个 $H_0$ 因子，对每个 $p$ 一致。对 $k$ 做单位化 Walsh 变换，用 $\chi(p+k)=\chi(p)\chi(k)$，得到

$$
K_X=\frac{2}{m}\sum_{w\ne0,\,\chi\in\widehat{Q_w}}
|h^{(0)}_{w,\chi}\wedge h^{(1)}_{w,\chi}\rangle
\langle h^{(0)}_{w,\chi}\wedge h^{(1)}_{w,\chi}|,
\qquad
h^{(b)}_{w,\chi}=a_{\phi_b}\sum_p\chi(p)\eta^{(b)}_{w,p}.
$$

这里 $K_X=q^{-1}\sum_L|a_ya_x\psi_L\rangle\langle a_ya_x\psi_L|$。每个 $\sum_p\chi(p)\eta^{(b)}_{w,p}$ 的斜矩阵是带符号的酉置换，所以收缩后的 $h^{(b)}_{w,\chi}$ 是 $R_b$ 中的单位向量，即使 $\phi_b$ 有复系数。固定 $w$，这些二形式由 Walsh 正交性彼此正交。不同 $w$ 的坐标边支撑不交。全族构成 $\Lambda^2 H_b$ 的正交基，范数平方皆为 $m/2$。在 $\phi_b^\perp$ 上 $a_{\phi_b}a_{\phi_b}^\dagger=I$，因而两个边缘算子均为恒等。

$$
\frac{2}{m}\sum_{w,\chi}|h^{(b)}_{w,\chi}\rangle\langle h^{(b)}_{w,\chi}|=I_{R_b}.
$$

使用了反对称稳定子基的坐标表达和 Clifford 对称性。[Sierant，Appendix C.1，Corollary 2](https://arxiv.org/html/2609.13106v2)

## 从两个边缘得到奇数维上界

令 $k=\dim Y$，$\Omega_Y$ 是其单位体积元。在 $\Lambda^k(R_0\oplus R_1)$ 上，记 $n_h=a_h^\dagger a_h$ 为单位向量 $h$ 的占据投影，$N_b$ 为 $R_b$ 的总粒子数算子。对 $h^{(b)}\in R_b$，$n_{h^{(0)}}n_{h^{(1)}}$ 投影到两根方向同时占据的子空间。其在 $\Omega_Y$ 上的期望为两根方向投到 $Y$ 后所张平行四边形的面积平方，即 $\|\Lambda^2 P_Y(h^{(0)}\wedge h^{(1)})\|^2$。因此 $B(X,Y)=\langle\Omega_Y,A_k\Omega_Y\rangle$，其中

$$
A_k=\frac2m\sum_{w,\chi}n_{h^{(0)}_{w,\chi}}n_{h^{(1)}_{w,\chi}}.
$$

单项占据投影乘积被其中任一投影控制。对上面的恒等边缘取外代数上的单粒子数提升，得 $A_k\preceq N_0$ 且 $A_k\preceq N_1$。每项保持两块粒子数，故在 $N_0=j,N_1=k-j$ 的分块上有 $A_k\preceq\min(j,k-j)I$。逐块取界即得所述上界。

## $d=16$ 全角度例

写 $R_\theta e_0=(\cos\theta,\sin\theta)^\mathsf T$，$R_\theta e_1=(-\sin\theta,\cos\theta)^\mathsf T$，$U=R_{\theta_2}\otimes R_{\theta_1}\otimes R_{\theta_0}$，$\phi=Ue_0$。固定二平面由 $\phi$ 的两个最高位副本张成。取 $Y$ 为 $Ue_1$ 和 $Ue_2$ 各自的两个副本，再加 $Ue_3$ 的最高位零副本。

当所有 $\theta_i\in(0,\pi/4)$，每个低位单比特因子都没有非恒等 Pauli 本征方向。一个 Pauli 若对整个 $X$ 是标量，则其最高位因子必为恒等，且所有低位因子必为恒等。因此 $X$ 不位于任何非恒等 Pauli 的本征空间内。八点仿射空间在四比特中是仿射超平面，其坐标支撑是一个 Pauli 本征空间，Clifford 共轭保持这一性质。$X$ 也不含稳定子态，因为其每个向量在三个低位均固定为上述纯因子，每个稳定该向量的 Pauli 只能在最高位非恒等。

将 $h_{w,\chi}^{(b)}$ 写回旋转基。每根 $h$ 由一个实斜 Pauli 矩阵作用于 $\phi$，整体符号无关。理由是固定 $w$ 的每条有向边以最显著差异位为零的端点为首，方向符号是陪集上的 Walsh 特征。把该特征延拓为低位空间的线性字符，并在方向 $w$ 上补上负号，得到矩阵 $X^wZ^z$，其中 $w\cdot z=1$。不同 $(w,\chi)$ 恰遍历所有 28 个这样的矩阵。

用 $J=XZ$ 记实斜单比特矩阵，令 $t_i=\sin^2(2\theta_i)$。在第 $i$ 个低位，旋转后的 $|0\rangle,|1\rangle$ 两坐标概率依单比特矩阵为

| 矩阵 | 概率 |
|---|---|
| $I$ | $(1,0)$ |
| $X$ | $(t_i,1-t_i)$ |
| $Z$ | $(1-t_i,t_i)$ |
| $J$ | $(0,1)$ |

斜矩阵含奇数个 $J$。由于 $Y$ 三个低位标签为 $1,2,3$，第 2 位固定为零，只有恰一个 $J$ 且位于第 0 位或第 1 位的项有贡献。若 $J$ 在第 $j$ 位，写 $A$ 为第 2 位坐标零概率，$r$ 为剩余的一位坐标零概率。那么 $Y$ 在两最高位块上的投影权分别为 $Ar+A(1-r)=A$ 和 $Ar$，故该项贡献 $A^2r$。剩余一位的 $I,X,Z$ 求和给 $\sum r=2$，第 2 位求和给 $\sum A^2=1+t_2^2+(1-t_2)^2$，再乘两个 $J$ 位置及系数 $1/4$，得到

$$
B(X,Y)=1+t_2^2+(1-t_2)^2=2-2t_2(1-t_2).
$$

因此保持 $\theta_0,\theta_1$ 为非 Clifford 角，令正 $\theta_2$ 下降至零，可从两个既知子类之外逼近 2。此极限的二平面具有一个稳定子低位因子，落入八点支撑类。

同目录上一级的 `rank7_five_set_structured_probe.py` 对三组 Pythagorean 角直接用整数行列式，按平行类精确加总所有坐标平面，得到同一公式的有理值。全为非 Clifford 角的例子取第 $0,1,2$ 位依次为 $(c,s,\ell)=(4,3,5),(12,5,13),(9999,200,10001)$，给出

$$
B=\frac{199840503809633398096050399840002}{100080028005600700056002800080001}
\approx 1.996807033252.
$$

本轮构造证明依赖两根方向可放在同一个 Pauli 的相反本征空间。一般没有这种分解的二平面仍待解决。
