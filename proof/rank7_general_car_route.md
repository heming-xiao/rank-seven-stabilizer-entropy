# 固定二平面五粒子算子界的 CAR 归约

2026-11-17。对任意复正交单位向量 \(x,y\)，取 \(R=\operatorname{span}(x,y)^\perp\)、\(W=W_{\mathrm F}\)、\(q=4/d\)。记 \(\beta:W\to\Lambda^2R\) 为 \(\beta=q^{-1/2}a_ya_x|_W\)。对 \(W\) 的正交归一基 \(\psi_L\)，置 \(\beta_L=\beta\psi_L\)，并在 \(\Lambda^kR\) 上定义

    A_k = Σ_L a_(β_L)† a_(β_L).

这里 \(a_\eta\) 是左楔乘 \(\eta\) 的伴随。对五维 \(Y\subseteq R\) 的单位体积元 \(\Omega_Y\)，已有 \(B(X,Y)=\langle\Omega_Y,A_5\Omega_Y\rangle\)。以下得到 \(A_5\preceq2I\) 的一个等价 Gram 不等式，并给出一个压缩估计的精确障碍。[已证子类与算子约定](reviews/rank7_two_link_independent_review.md)

## 三个自由坐标的正规序

定义

    Q = β†β on W,
    C: R⊗W → Λ³R,        C(r⊗ψ) = r∧βψ,
    T: Λ³R⊗W → Λ⁵R,      T(γ⊗ψ) = γ∧βψ.

则 \(CC^\dagger=A_3\)，\(TT^\dagger=A_5\)。对 \(r\in R\)，\(r\wedge\beta\psi=q^{-1/2}a_ya_x(r\wedge\psi)\)，所以 \(C\) 是 Theorem 20 的算子在 \(R\otimes W\) 上的限制并除以 \(\sqrt q\)。故 \(A_3\preceq I\)。Theorem 17 的均匀占据给 \(Q\preceq I\)。[Sierant，Theorem 17、Theorem 20](https://arxiv.org/html/2609.13106v2)

固定 \(R\) 的任意复正交归一基 \(r_a\)，简记 \(a_a=a_{r_a}\)。在 \(R\otimes W\) 上定义 Hermitian 交叉 Gram

    H_(a,b) = (a_b β)† (a_a β),
    H^[3] = Σ_(|E|=2) (a_E†⊗I) H (a_E⊗I) on Λ³R⊗W,

其中 \(a_E\) 是升序坐标楔积 \(r_E\) 的厄米收缩。令 \(V=C^\dagger:\Lambda^3R\to R\otimes W\)，在 \(W\otimes W\) 上以 \(\Sigma\) 表示通常的交换，定义

    S^[3] = (V†⊗I)(I_R⊗Σ)(V⊗I).

精确正规序给

    T†T = I⊗Q − H^[3] + S^[3].                         (1)

为核对系数，取两个单位坐标三楔 \(r_I,r_J\)，相应矩阵元写成 \(\langle\beta\psi,a_I a_J^\dagger\beta\phi\rangle\)。在 CAR 展开中，一个收缩集合 \(E\subseteq I\cap J\) 留下正规序项 \(a_{J\setminus E}^\dagger a_{I\setminus E}\)。其符号为 \((-1)^{3-|E|}\epsilon(I,E)\epsilon(J,E)\)，其中 \(\epsilon(I,E)\) 是 \(r_E\wedge r_{I\setminus E}=\epsilon(I,E)r_I\) 的符号。可由先在两个三楔中分别将 \(E\) 移至最前面，再让余下的湮灭与创造算符交叉得到。每个 \(E\) 相当于选择 CAR 中哪些配对取 Kronecker delta。

- \(E\) 大小三给 \(\delta_{IJ}Q\)。
- \(E\) 大小二给所写的 \(-H^{[3]}\)。
- \(E\) 大小一对每个剩余无序坐标对 \(I',J'\) 给 \(+(a_{J'}\beta)^\dagger(a_{I'}\beta)\)。这个两坐标交叉 Gram 就是 \((\beta\otimes I)\Sigma(\beta^\dagger\otimes I)\)。其所有单坐标收缩之和给 \(S^{[3]}\)，因为 \(V\gamma=\sum_a r_a\otimes\beta^\dagger a_a\gamma\)。
- \(E\) 为空时右端三个湮灭算符消去二形式 \(\beta\phi\)，故为零。

所有和均按无序坐标子集计一次。\(\|V\|^2\le1\) 表明末层本身满足 \(-I\preceq S^{[3]}\preceq I\)，无需逐个剩余坐标松弛。

## 交换层的对称性给出等价的联合 Gram 界

定义 \(D_{\mathrm{as}}=(A_3\otimes I)-S^{[3]}\)。有

    D_as = (V†⊗I)(I_R⊗(I−Σ))(V⊗I),    0 ⪯ D_as ⪯ 2I.

对任意 \(\Omega\in\Lambda^5R\)，

    (V⊗I) T†Ω = Σ_(L,M) a_(β_M) a_(β_L) Ω ⊗ ψ_M ⊗ ψ_L.

两个度二湮灭算符交换，所以右侧在 \(W\otimes W\) 的交换下对称，故 \(D_{\mathrm{as}}T^\dagger=0\)。因此 \(T^\dagger T\) 和 \(D_{\mathrm{as}}\) 的支撑正交。由 (1) 得

    A₅ ⪯ 2I
      iff T†T + D_as ⪯ 2I
      iff H^[3] ⪰ I⊗Q + A₃⊗I − 2I.                    (2)

最后一行是待证的联合 Gram 下界。等价关系用到了 Theorem 20 的 \(A_3\preceq I\)。

## Pair exchange 所给的界与单独估计的障碍

对一个自由坐标，CAR 给 \(C^\dagger C=I\otimes Q-H\)。从 \(CC^\dagger\preceq I\) 可得 \(H\succeq I\otimes Q-I\)。把该式应用于每个坐标二收缩后相加，只有 \(H^{[3]}\succeq3(I\otimes Q-I)\)。因 \(Q\preceq I\)，该式不足以推出 (2)。

直接在交叉 Gram 上用 Theorem 18 有一个额外占据投影。令 \(U_b=a_ba_x|_W\)，则

    H_(a,b) = q^(−1) U_b† n_y U_a.

交换 \(a_y\) 和 \(a_a\) 所得两个负号相消。Theorem 18 将完整的 \(q^{-1}U_b^\dagger U_a\) 交叉 Gram 转成 holomorphic Gram，现式在两者间含 \(n_y\)。由 C.8 的占据分解 \(a_x\psi=A_x\psi+y\wedge a_ya_x\psi\)，完整 Gram 等于该占据项加仅含 \(A_x\) 的空项。C.8 的 Theorem 21 输运与 pair exchange 解耦的是 \(CC^\dagger\) 在 \(\operatorname{ran} A_x\oplus\operatorname{ran} A_y\) 上的块。这说明了 \(A_3\) 界，仍需额外估计该空项和三阶 lift 的联合式。[Sierant，Theorem 18、Theorem 21、Lemmas 12–13、Proposition 8](https://arxiv.org/html/2609.13106v2)

一个看似更简便的充分条件 \(H^{[3]}\succeq I\otimes Q-I\) 实际不成立。如下例同时确认 (1) 的符号及 (2) 中 \(A_3\) 项的作用。

取 \(d=8\)、\(x=e_0\)、\(y=(e_1+e_2)/\sqrt2\)。在 \(C_4=\{4,5,6,7\}\) 上，四个有贡献的方向 \(L\) 对应以下边 \(e\)，其二形式为 \(\beta_e=r_e/\sqrt2\)，其中 \(r_e\) 是升序计算基二楔。

| 边 \(e\) | \(L\setminus\{0\}\) |
|---|---|
| 45 | \(\{1,4,5\}\) |
| 67 | \(\{1,6,7\}\) |
| 46 | \(\{2,4,6\}\) |
| 57 | \(\{2,5,7\}\) |

余下的非零二形式来自 \(\{1,2,3\}\)，其支撑为 \(\operatorname{span}(e_3,(e_1-e_2)/\sqrt2)\)。取 \(s=e_3\)、\(\Omega=s\wedge e_4\wedge e_5\wedge e_6\wedge e_7\)。对每条表中边 \(e\) 定义 \(\gamma_e=\pm s\wedge r_{C_4\setminus e}\)，符号使 \(\gamma_e\wedge r_e=\Omega\)。令

    Ψ = (1/2) Σ_e γ_e⊗ψ_e.

\(\Psi\) 是单位向量，\(T\Psi=\sqrt2\,\Omega\)，且 \(\langle I\otimes Q\rangle_\Psi=1/2\)。在 \(V\gamma_e=\sum_a r_a\otimes\beta^\dagger a_a\gamma_e\) 中只有 \(a=s\) 一项非零，因为另一种收缩留下 \(s\) 与 \(C_4\) 的一个坐标，所有 \(\beta_L\) 在这种混合边上都为零。因此 \(V\gamma_e=\pm s\otimes\psi_{C_4\setminus e}/\sqrt2\)。互补边的定向符号相同，故 \((V\otimes I)\Psi\) 对称且范数平方为 \(1/2\)。因此

    ⟨S^[3]⟩_Ψ = ⟨A₃⊗I⟩_Ψ = 1/2,
    ⟨H^[3]⟩_Ψ = 1/2 + 1/2 − 2 = −1.

这小于单独充分条件的右端 \(-1/2\)，而恰等于 (2) 的右端 \(1/2+1/2-2=-1\)。\(x=e_0\) 的已证算子界在此饱和。一般算子界或物理 \(B\) 的违反均未由此得到。

## 仅保留低阶算子约束的限制

若只使用 \(Q\preceq I\)、\(A_3\preceq I\) 和精确一体边际，再对任意二形式框架应用 CAR，无法推出 (2)。例如取抽象的 14 维 \(R\)，在坐标上放两个互不相交的五环和两条独立边。对每条边 \(e\) 给一个 \(\beta_e=\sqrt{w_e}\,r_e\)，五环的边权为 \(1/2\)，另两条边权为 1。每个坐标的加权度数恰为 1，所以一体边际为恒等。不同边的二楔正交，且 \(w_e\le1\)，故 \(Q\preceq I\)。在坐标三楔上，\(A_3\) 的本征值为该三点的内部边权。图无三角形，且度数为 1，故每个内部边权至多 1，得到 \(A_3\preceq I\)。但一个五环的坐标五楔取到 \(A_5\) 的本征值 \(5/2\)。

这是说明以上低阶约束为何不足的抽象二形式框架。它未被实现为反对称 stabilizer 投影的双收缩，也会违反物理紧框架的奇数割泄漏下界。[物理泄漏下界](rank7_fractional_cycle.md)
