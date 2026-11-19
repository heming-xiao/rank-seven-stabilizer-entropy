# 秩七最高对分裂、并列最高及双探针支付的独立复核

完整并列最高定理通过核验。任意正尾概率与并列最大的两条概率组合，在任意量子比特切割及复局部酉下都达到排序计算基最优，且每个这种谱有允许打破并列的相对秩七开邻域。一般排序谱的两个附加充分条件和秩六端点也通过。本轮仍未证明所有秩七谱。[并列最高定理](../rank7_equal_highest_pair.md) · [两探针谱区域](../rank7_two_probe_separation_and_tail_region.md)

## 最高两概率抬升的加权亏量

记 `h=α−β,k=β−γ,q=γ−a,g=hq,m=h+k+q,Δ=km`。基谱将最高两概率同时减去 `k`。只改变一个尾分量 `γ=a+q` 时，最高对加权差 `Y(q)=Y(0)−qD_A`，其中 `D_A=a−Σ_(i≥3)t_iw₀₁₂i≥0`，由固定三腿全补权至多一。令 `L(q)=2(a+q)Y(q)+V₀(q)+V₁(q)`。直接展开得

```text
L(q)−qY(q)=L(0)+q[Σ_(i<j)r_i r_j δT_ij−3a D_A]−q²D_A。
```

这里 `T_ij` 合计三种领先对加剩余尾对 `i,j` 的四楔权。旧补对约束恰给 `T_ij+A_i+A_j≤1`，其中 `A_i=w₀₁₂i`，且参考取等。乘 `r_i r_j` 相加，化简为 `Σ r_i r_j δT_ij≤(b+c+d)D_A−Σ_i r_i(a−r_i)A_i≤(b+c+d)D_A`。再用最高同时抬升的精确式 `E−E₀=k(h+k)Y+kL(q)`，得到 `E−E₀≤ΔY−kq(q+3a−b−c−d)D_A`。`q=0` 时 `L(0)≤0` 来自含一个 `b₁` 且另三域在 `3…6` 的 20 条独立前向证书，故这一结论也覆盖并列极限。[最高对证明](../rank7_highest_pair_split_loss.md)

更强的 `L(0)≤−bcd v₁` 使用其中五个先前未保留的前向亏量。三槽指标 `456,466,556,566,666` 在 `bcd` 中的重数确为 `1,1,1,2,1`。运行最终核验器后， 35 个三次成本、1225 个列约束以及交换最低两个计算基标签的物理取等式全部通过。我用独立的四楔排列展开及补图容量行语义又重算了同一 1225 个列约束，均非负并精确达到参考值。保留强弱两界等价于在 `E−E₀` 额外扣 `k bcd(v₁)_+`。[精确核验器](../../verification/verify_rank7_highest_pair_split_loss.py)

## 任意尾的并列最高及严格余量

当 `α=β=1`，基谱前三概率全等，故前向例外价格全部消失并给 `E₀≤0`。如果 `Y≤0`，新最高对界立即给 `E≤E₀+(1−r)(1−t)Y≤0`。如果 `Y>0`，设旧并列最高正分支的 `Γ=1−r−t−a−b+s`。按尾对补容量加权再用两槽前缀比较，`E≤ΓY`，所以 `Γ≤0` 也直接给外积比较。

剩余 `Y,Γ>0` 时，先前独立复核的匹配极化给 `2⟨u₁,L_-⟩≥μκ₁+Y`，其中 `μ=(1−r)(1−t)≥4s²`。前缀与固定二楔几何给 `κ₁≥Y/(4s²)`。混合支付至少 `3(μ+4s²)²Y/s²`。最高双腿块的最小振幅 `√(bs)` 与块外最大振幅上界 `√(rta)` 给另一个压缩支付 `64(√(bs)−√(rta))_+²Y/s²`。小 `s<2/21` 直接由 `(1−s)²>7s` 和 `p=1−r−t>s` 得到严格支付。在 `s≥2/21`，依次把 `b,a` 降至 `s` 只会降低净支付，对第二个待降参数的导数下界为 `168s²−16s≥0`，因此只需 `√r≤9/10` 的两盒类。重跑原脚本得到 `26,8` 个严格正有理盒，与先前独立反向轴分箱 `56,13` 一致覆盖全部域。由于严格比较的支付与增益均是固定谱系数乘 `Y`，可从实际支付保留固定正比例。其他分支保留全部缺陷。这就给允许七个概率全异的相对开邻域。[正分支及严格余量复核](rank7_tied_head_prefix_independent_review.md) · [开邻域转移](rank7_open_interior_independent_review.md)

## 平移两探针和一般谱的充分条件

按实 Hilbert–Schmidt 内积，`2⟨u,L⟩≥H_sh+Δc₁`，`2⟨u₁,L⟩≥Y+Δκ₁+g c₁`。最高对第二项的 `gc₁` 来自完整条件匹配中的 `g(1−p)` 项乘 `p₁` 的平均。尾扣量及剩余的领先类别扣量均非负。展开一次 `||L−s u−t u₁||²` 的交叉系数恰为 `24(sΔ+tg−st)c₁`。当共享支有正增益，`ν>0,g>16b²`，选择 `s=(H_sh)_+/κ≤g+12cd<2g`，其中用 `U≤cdν≤12cdκ`。其他支选 `s=0`。因此 `0≤t≤2Δ` 时交叉系数非负，因为它关于 `t` 线性且两端非负。整个推导仅使用一次实际混合范数。

对共享支，留出一半反对易支付而将小缺陷标量项由 `g²/12` 降至 `g²/24`，仍可按 `S=cd` 的单调性移到 `S=b²`。令 `x=√[g/(3b²)]`、`y=x−4>−2`，归一净差乘 `4/3` 的恒等式为

```text
(25/2)x⁴−576x²+1344x+752
 = [(25/2)(y+8)²−176]y²−64y+112
 ≥274y²−64y+112>0。
```

右式判别式严格为负。大缺陷原式只需要一半反对易支付，故无需更改。实际 `U=U₀−kD_A`，前向亏量 `B₁≥qD_A` 支付新的共享亏量而保留最高对负价至少 `Δ−kh/2≥Δ/2`。因此该负价在外积系数 168 下大于任何 `t≤2Δ` 产生的 `24t B₁`。若共享外积支非正直接设 `s=0`，若 `ν≤0` 则仅用 `E₀≤0` 并跳过共享亏量即可。

在 `t=Δ`，最高对混合与反对易余量至少 `(12Δ²+R)κ₁+g²κ/2`，其中 `R=k²[k²+(h²+q²)/2]`。几何 `v₁⁺≤4κ₁` 与 `v₁⁺≤12κ` 给生产稿的充分条件；取 `P=0` 使用基本最高对比较，取 `P=k bcd` 使用独立验证的五个额外系数。若 `v₁≤0`，未取正部的剩余最高对价 `144d²Δ v₁` 本身非正。另取 `t=(1+z)Δ`、`z∈[0,1]` 时，可增加的有效支付为 `24zΔd²−3z²Δ²`，最大值在 `z=min(1,4d²/Δ)`，给文中两个精确区间。共享反对易剩余也可用 `q⁴J₃₃`。奇秩漏出不等式保证漏出小于 `1/2` 的标签对易；最大对易退相干和前三坐标舍入给三空间漏出至多 `4J₃₃`。这三坐标包含在某个仿射四点码内，固定块常数 18 给 `v₁⁺≤72J₃₃`。同一份剩余反对易只取 `g²/24,q⁴/72` 两个系数的较大者。由 `R≥Δ²/5`，附带的两个充分阈值 `Δ≥(2880/61)d²` 和 `g≥203d²` 也直接通过。[联合充分条件与改进项](../rank7_leading_split_joint_payment.md)

## 一般谱的近尾区域

记 `T=b+c−d`、`A_*=γ+a−d≥T`。前缀给 `E−E₀≤k(m−T)Y−kq A_*D_A`，最高对基本价另给 `E−E₀≤kmY`。若 `m≤T`，以权 `m/T` 合并两界，恰消掉 `Y` 并留至少 `kgD_A/2` 给共享修正。若 `T<m≤7T/5`，则 `A_*>h/2` 且 `k(m−T)≤2Δ/7`。于是 `Y≤0` 时直接舍去其负项，`Y>0` 时取 `t=2Δ` 支付 `48ΔY`，至少等于外积的 `168k(m−T)Y`。该选择保留全部共享混合项。共享损失用上式已经保留的 `kgD_A/2` 修正，故原等中间逐标架支付适用。

严格余量在边界 `m=7T/5` 仍成立。若最高分支有正价，必有 `k>0,Y>0`，所以未用的 `Rκ₁` 至少是正的谱系数乘 `Y`，因 `Y≤4d²κ₁`。共享正价分支的严格余量是正的谱系数乘 `ν`。如果只有一个分支有正价，另一个直接保留剩余缺陷。对每个固定谱，这些正余量与各自的有限增益上界足以统一保留一部分总实际缺陷，从而用既有转移定理得到相对开邻域。[近尾区域正文](../rank7_two_probe_separation_and_tail_region.md)

六腿端点还独立验证了两个自然半价格能同时支付。直接做末概率仿射插值时，最高对几何尺度从 `c²` 变成 `cd`，因此需要额外比较才能恢复正向证书的 `d²`。[秩六结论](../rank6_two_probe_endpoint_independent.md) · [标准库精确核验](../../verification/verify_rank6_two_probe_endpoint.py)

## 最高对常数 (5/2) 和压缩补项

对 `κ₁≤2/15`，最大斜权 `P≥13/15` 高于 `(1+1/√2)/2`。自适应阈值 `t=1/2+√[P(1−P)]` 使所有高权差标签在秩二平面中的 Pauli 期望模大于 `1/√2`，因二维斜块乘积的下界是两个斜振幅乘积减去漏块范数乘积。`5P+3t≤4+√34/2<104/15≤8(1−κ₁)` 给高标签质量大于 `5/8`，足以由斜陪集奇计数确定秩二码。既有四阶估计的两个端点 `9/64,6137/40000` 均大于 `2/15`，故码楔重叠模 `a₀>19/20`，且 `κ₁≥3(1−a₀)`。

两组共用稳定子腿的正压缩给前三项下界 `−2b₀b₁`，再用 `2I−L≥0` 对互异单偏离交叉和 `b₀b₁` 作二维 Cauchy–Schwarz，合计损失至多 `4ε`。双偏离贡献至多 `(5/2)ε+ε²/2`。由于 `ε≤1−a₀<1/20`，近区得 `87κ₁/40`。远区由物理上界 `1/3≤(5/2)κ₁`。这独立验证了 `K=5/2`。更强阈值 `κ_*=(8−√34)/16` 的陪集计数只需高质量至少 `5/8`，计算后的全域常数 `8(8+√34)/45≤32/13` 也成立。[最高对几何](../rank7_highest_pair_geometry_five_halves.md)

用 `v₁⁺≤Kκ₁` 替换联合充分式中的单对几何后，最佳单对平移取 `min(1,Kd²/Δ)`，恰给正文 `Φ_K`。两个振幅侧分别用双高四楔最小 `√(αβcd)` 和其他四楔最大 `√(αγab)`。若存在正间隙 `σ`，最高对归一压缩迹 `2+v₁` 的鸽巢损失乘 `96σ²` 至少 `64σ²v₁`，是独立于前两种 Pauli 缺陷的真实余量。由此最终联合充分式的 `K=5/2` 与附加 `64σ²` 均通过。[最终联合式](../rank7_leading_split_joint_payment.md)


## Final geometry and compression audit

The root independently checked the final highest-pair geometry. With
\(P=\max p_b\) and \(t=1/2+\sqrt{P(1-P)}\), \(\kappa_1\le2/15\)
implies \(P\ge13/15>t\) and \(5P+3t\le4+\sqrt{34}/2<104/15\).
The high mass exceeds \(5/8\) so the stabilizer code construction
applies. The fourth-moment bound at \(3/4,19/20\) gives
\(\kappa_1\ge3e\). Positivity of \(2I-L\), combined with the
two-coordinate Cauchy–Schwarz on the single-leak terms, bounds
their contribution below by \(-4\epsilon\), including their
interaction with the reference wedge. The double-leak terms then
give \(v_1^+\le(13/2)\epsilon+\epsilon^2/2 \le87\kappa_1/40\)
in the small-defect regime. Otherwise \(v_1\le1/3\) gives the
uniform bound \(K=5/2\). [Geometry](../rank7_highest_pair_geometry_five_halves.md)

In the final joint criterion the shifted mixed payment adds
\(\max_{0\le z\le1}(24z\Delta d^2-12z^2\Delta^2/K)\), attaining its
maximum at \(\min(1,Kd^2/\Delta)\) when \(\Delta>0\).
The highest-pair four-wedge block has amplitude at least
\(\sqrt{\alpha\beta cd}\), and its complement at most
\(\sqrt{\alpha\gamma ab}\). With a positive gap between them,
the trace is \(2+v_1\) and \(96\phi(2+v_1)\ge64v_1\) for
\(0<v_1\le1/3\). This compression payment is disjoint from the
actual mixed and anticommuting payments. [Final criterion](../rank7_leading_split_joint_payment.md)
