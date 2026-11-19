# 第二轮独立审核：谱交换前提与局部最优性

日期：2026-11-17。针对 [Liu–Cui 2609.01993v2 Appendix C](https://arxiv.org/html/2609.01993v2) 前一轮留下的 Eq.97 依赖，主 agent 和 methods agent 独立推到了相同的二点压缩证明。本笔记记录目标函数、相位与归一化的连接，以及局部最优性论证的补全。它是文献理解与证明复核，不是一般 CB 猜想的解答；没有新颖性或发表主张。

## 1. 从 Hermitian Pauli 矩到非负配置计数

令 V=F2^m，d=2^m，f:V→[0,∞)，暂不要求归一化，alpha 为整数且 alpha>=2。记

    W_s(k) = sum_x (-1)^(k·x) f(x) f(x+s).

对 Hermitian Pauli X^s Z^k 加上其约定相位后：若 s·k 为奇数，W_s(k)=0，因为 x→x+s 使和式变号；若 s·k 为偶数，相位为 ±1，取 2alpha 次方后消失。因此

    zeta_alpha(f) = (1/d) sum_(s,k) W_s(k)^(2alpha).

展开并用字符正交性，得到精确恒等式

    zeta_alpha(f)
      = sum_s sum_(x1+...+x_(2alpha)=0)
          product_(j=1..2alpha) f(xj) f(xj+s).              (A)

这里没有额外的 d：字符求和给出的 d 正好抵消前面的 1/d。令最后一个 x 为之前 2alpha−1 个 x 的 XOR，独立变量就是 s,x1,...,x_(2alpha−1)，共 2alpha 个 V 变量。右端是 4alpha 个**同一非负函数的齐次 F2 线性形式**的乘积和。

这一步也说明为什么不能对非整数指数直接照抄组合展开。

与二分参考态的关系也可独立看出：跨分割的按位 CNOT 把 sum_x f(x)|x,x> 变成 |f>⊗|0>，M_alpha 的全局 Clifford 不变性及纯 stabilizer spectator 的可加性给出同一数值。这仅用来计算固定参考态的熵，不把该跨分割门当作允许的局部优化。

## 2. 对任意齐次线性配置的二点压缩

给定非零 delta∈V，取其最高非零 bit 位置 h，令 H={q:q_h=0}。于是 V=H⊕<delta>，且对所有 q∈H，整数标签满足 q<q+delta。

写

    f(q+epsilon delta) = A(q)+(-1)^epsilon B(q),
    A(q)=[f(q)+f(q+delta)]/2 >=0,
    B(q)=[f(q)-f(q+delta)]/2.

把每对中的大值放到 H 的二点压缩 C_delta，恰好保持 A 并将 B 换成 |B|。

考虑任意 k 个 V 变量及齐次 F2 线性形式 L1,...,Lr，定义

    T(f) = sum_(z in V^k) product_(j=1..r) f(Lj(z)).

将每个 z 分成 H 分量和 delta 分量。展开 A/B 后，对 k 个二元 delta 分量求和：子集 S 的字符和等于 2^k（当 sum_(j in S) Lj=0）或 0（其它情况）。因而

    T(f)=2^k sum_(q in H^k)
            sum_(S: sum_(j in S) Lj=0)
              product_(j in S) B(Lj(q))
              product_(j notin S) A(Lj(q)).                (B)

子集条件是线性形式的**系数向量之和为零**，即恒等为零，不是仅在当前 q 上取值为零。每项系数非负、A 非负；逐个将 B 换成 |B|，每个单项都不减。因此

    T(C_delta f) >= T(f).                                 (C)

允许形式重复或为零，不影响字符正交性。这里要求齐次形式、非负实函数，不能无说明推广到带任意常数项或复函数。

同类压缩的原始数学依据见 [Huczynska–Rakhmonov–Yip 2609.07855v1](https://arxiv.org/html/2609.07855v1)，§3 定义 v-compression，§4.4 给加法元组的非负函数重排。该文 Theorem 4.9 是单个加法约束；本笔记通过(B)直接处理(A)的耦合线性形式，而不是将4.9无证明地套用。

## 3. Eq.97 需要的单次交换比较

若 f 已按二进制整数标签递减排列，任取 i<j，令 delta=i+j（XOR）。最高不同 bit 上 i 为0，因此 i∈H，且所有 delta 对都已经大值在 H。

交换 f(i)、f(j) 得 g。它只把对应一对的 B 改了符号；其它对不变，故 C_delta g=f。将(A)代入(C)，得到

    zeta_alpha(f) >= zeta_alpha(g).                       (D)

这正是前一轮尚未核实的排序前提。**此依赖现已由自包含推导得到支持，不再仅凭“未找到引文”悬置，也不能把它称为已经发现的原文错误。**

### 全部基排列与 monomial 局部酉

更一般地，反复选择会改变当前 f 的 C_delta，每次都严格增加位置势

    P(f)=sum_x (d-1-x) f(x).

压缩仅重排固定有限 multiset；若存在 i<j 但 fi<fj，取 delta=i+j 就会改变至少该对。因此有限步后必为递减排列。结合(C)，递减代表在**全部基标签排列**中最大化 zeta_alpha。

在两边各自采用 monomial 酉（置换×任意对角相位）的情形，单酉表达 U Sigma U† 中相位消掉，仅剩置换。逐边应用排序比较，再用两酉 Cauchy–Schwarz 界，得到两边不同的置换和相位也不能超过 CB 值。

所以早期仅检查共同标签排列的程序，今后只作为定义/实现复核保留，**不再是寻找主猜想反例的路线**。这个结论仍不覆盖一般酉矩阵中的相干基混合。

## 4. 从曲率符号到真正的局部最优

原文的严格凸性步骤需只使用奇数 r=2alpha−1 的 Pauli 系数幂映射。其正性可由 r 份 PSD 态、奇数复制的逻辑 Pauli、部分迹以及（必要时）整个输出的全转置给出。全转置保持正性，这里不是部分转置。

奇数限定不可省略：两 qubit Bell 密度矩阵的 Pauli 系数在 r=2 时给 T_2(rho)=(II+XX+YY+ZZ)/4=SWAP/2，反对称子空间本征值为 −1/2。所需的 r=2alpha−1 始终为奇数，故这个边界例不影响本笔记的证明，也不是 CB 猜想反例。

Hessian 非负给 zeta_alpha 在实振幅空间上的凸性。沿任意非零方向 v，它是最高次系数 zeta_alpha(v)>0 的 4alpha 次多项式，不能在任何区间成为仿射函数，因此严格凸。

令 gi=partial_i zeta_alpha(f)。严格凸性应用于交换 i,j 的两个不同点，结合(D)，得到当 fi!=fj 时

    cij=(fi-fj)(gi-gj)
       > zeta_alpha(f)-zeta_alpha(swap_ij f) >=0.

原文的二阶变化为

    zeta_alpha(exp(itK) Sigma exp(-itK))
      = zeta_alpha(Sigma)-t² sum_(i<j) cij |Kij|²+O(t³).

因此所有连接不同特征值块的方向严格降低 purity；零二次项方向恰是 [K,Sigma]=0，它们保持该矩阵不变。模掉这些对易对称后，固定谱酉轨道上的 Hessian 负定，确实得到局部极大 purity，而不只是“半定所以极大”的跳步。两酉情形再用单酉归约里的 Cauchy–Schwarz 界，得到相应局部最优性。

为核清高阶余项，原文 Eq.80 的 off-diagonal 至少四因子理由也已检查：平移不在对角子群时，每个配对至少一个 off-diagonal，合计2alpha>=4；平移在子群时，一个外部指标给两因子，但 XOR 约束排除恰好一个外部指标，故仍至少四个。

这补清了我们上一轮保留的局部最优性逻辑。**局部最优仍不推出一般全局最优。**

## 5. 精确算术校验与其限度

运行 `compression_proof_check.py`：5组固定整数振幅、alpha=2/3，比较 Walsh 矩、约束线性配置枚举、SymPy Hermitian Pauli 矩阵三种表达，10组精确恒等式全部一致。另有180个确定性压缩/交换校验通过。没有随机采样、没有局部酉优化。

alpha=2 的 cube 分类还独立重现系数 1、14、168、1344，分别对应支撑仿射维数0、1、2、3；系数来自 2^r×product_(j=0..r-1)(8−2^j)。这检查了归一化，不以有限枚举代替上面的全维证明。

输出：`compression_proof_check.json`。当前结论是“该文献依赖已独立补核”，不是“发现了一篇新论文的成果”。
