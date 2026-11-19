# Schmidt 秩七的两类谱锥独立复核

两组有理对偶证书均通过独立复核。令 `t₀≥…≥t₆>0` 为 Schmidt 概率。任一条件 `t₀/t₄≤3` 或 `1/t₃−1/t₁≤1/t₀` 成立时，排序计算基代表在任意量子比特二分割及全部局部酉的轨道上达到最小二阶稳定子 Rényi 熵。这两个条件都允许最大与最小非零概率之比任意大。

## 参数与缩放

取 `a_i=1/t_i`，`b₀=a₀`、`b_h=a_h−a_(h−1)`。两类中均取 `z_h=b_h≥0`（`h≥1`）。

| 谱锥 | `z₀` | `z₀≥0` 的等价条件 | 各线性因子 |
|---|---|---|---|
| 最大五个概率比值 | `a₀−(a₄−a₀)/2` | `a₄≤3a₀`，即 `t₀/t₄≤3` | `2a_i=2z₀+Σ_(h=1)^6 [2·[h≤i]+[h≤4]] z_h` |
| 中段倒数差 | `a₀−(a₃−a₁)` | `a₃−a₁≤a₀`，即 `t₃≥t₀t₁/(t₀+t₁)` | `a_i=z₀+Σ_(h=1)^6 [[h≤i]+[h∈{2,3}]] z_h` |

第一类的三元组目标因子为 8，第二类为 1。两类允许全部等号与重根。尾部 `t₅,t₆` 只受有序、正值与 Schmidt 概率归一化制约。归一化对两个条件均无影响。

## 精确验证与物理结论

验证器按 35 个三元组独立连续乘入三个线性因子，展开整数三次系数。随后从四重楔积的占据规则重建 21 个点对、35 个四点集和 42 个有序点对行。三类物理约束分别来自 Corollary 4、Theorem 17、Proposition 10。计算基 Fano 参考向量满足全部 98 行。使用这些行验证全部稀疏对偶价格并以标准库 `Fraction` 核对精确目标。两组证书只使用三类已知约束。[98 行物理约束复核](rank7_ambient_independent_review.md) · [原文](https://arxiv.org/html/2609.13106v2)

| 谱锥 | 单项式记录 | 对偶不等式 | 计算基取等 | 精确目标等值 | 正乘子 |
|---|---:|---:|---:|---:|---:|
| 最大五个概率比值 | 84 | 2,940 | 588 | 84 | 882 |
| 中段倒数差 | 84 | 2,940 | 588 | 84 | 598 |

每组有 75 个实际出现的单项式与 9 个零单项式，均列入核验。以非负单项式加权逐系数界，再除以相应缩放因子，即得 `c_F(N²)≤c_F(M²)`。Proposition 2 和 Theorem 7 在计算基同时取等，由 Corollary 1 即得全部局部酉的结论。非平衡切割可按原文 Sec. III.1 填充稳定子辅助比特，七个正 Schmidt 概率与两种条件均保留。[原文](https://arxiv.org/html/2609.13106v2)

可在项目目录运行 `python verify_rank7_unbounded_spread_dual.py rank7_unbounded_spread_dual.json --output independent_rank7_unbounded_spread_dual.json` 复现。证书 SHA256 为 `b16931521b33688e8adebeef5fa8a03fc6912e92c0fe1fd37a41e962e4a889c9`。[证书](../../certificates/rank7/rank7_unbounded_spread_dual.json) · [验证器](../../verification/verify_rank7_unbounded_spread_dual.py) · [证据](../../certificates/rank7/independent_rank7_unbounded_spread_dual.json)
