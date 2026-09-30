# 金石等 (2008) Wishart 论文形式化：定理追踪表（B0）

建立：2026-09-27 后（S 会话）。**性质声明：本表由 S 依据仓库内已核验来源起草**
（`notes/jin_2006_wishart_summary.md`、`theory/jin_wishart_formalization/README.md`、
以及 S 实际读过的 Lean theorem 陈述）。B0 卡片原归 C 负责：**论文原文的逐条核对
（精确方程编号、参数域、记号约定）仍待 C 对照 arXiv:cs/0611007 PDF 完成**，
在此之前，所有依赖原文细节的单元格标 `[待核实]`，不得声称"逐条对齐"。

## 状态图例（按执行计划第 0 节的五个验收维度）

```text
陈述   = 论文定理的 Lean 陈述已固定（含假设与参数域）
基础设施 = 所需定义/测度/特殊函数已构建
模型→公式 = 从真实概率模型证到公式候选
公式→结论 = 公式候选等于论文结论（概率等式闭合）
审查   = 独立人工审查通过（测度论步骤）
```

| 维度取值 | `未陈述` / `仅公式侧` / `候选` / `已证` / `审查通过` |
|---|---|

## 主表

| 论文条目 | 原文假设/参数域 | 概率模型 | 原结论 | 对应 Lean（文件 : theorem） | 状态 | 缺口与证据 |
|---|---|---|---|---|---|---|
| **Theorem 1** 最小特征值 CDF（Nuttall Q + 上不完全 Gamma 的行列式比值） | `s=min(n,m)`, `t=max(n,m)`, `L≥0` 秩非中心，空间白化复高斯，完美 CSI `[待核实：精确方程编号]` | 非中心复 Wishart 有序特征值 `φ₁>…>φₛ>0` | `P(φₛ≤x)` = 行列式比值 | 公式侧：`Theorem1Formula.lean : theorem1CdfCandidate`；中心单列任意行：`WishartGamma.lean`；非中心 `1×1`：`ScalarNoncentralTheorem1.lean`；**`2×1` 任意非零复均值：`Theorem1TwoRowsActualCDF.lean : theorem1TwoRowsCandidate_eq_actualCDF`**（+ 中心分支）；**`3×1` 单列非中心任意均值方向：`Theorem1ThreeRowsActualCDF.lean : theorem1ThreeRowsOneColumnCandidate_eq_actualCDF`**（`λ>0,x≥0,‖encodedMean‖²=2λ`）；直接 Frobenius 参数推论：`Theorem12ThreeRowsFrobeniusCDF.lean : theorem1ThreeRowsOneColumnCandidate_eq_actualCDF_frobenius`；单列任意行仅公式侧：`Theorem1SingleColumnAnyRows.lean` | 陈述✅ 基础设施✅ 模型→公式：`2×1` 任意均值✅ / `3×1` 任意均值方向✅ / 一般❌；公式→结论同范围；审查❌ | 一般 `(s,t,L)` 未证；分母非零覆盖已闭合的 `1×1`、`2×1` 与此 `3×1` 单列特例；`2×1`、`3×1` 的换元/球面积分/Fubini 标 `[需人工审查]`；论文竖线=行列式 vs Lean 候选对复行列式取模长，等价性未证 `[待核实]` |
| **Theorem 2** 最大特征值 CDF（Nuttall Q 差 + 下不完全 Gamma 的行列式比值） | 同上 | 同上，`φ₁` | `P(φ₁≤x)` = 行列式比值 | 公式侧：`Theorem1Formula.lean : theorem2CdfCandidate`（含 `Ξ(x)+Ψ(x)=Ψ(0)` 逐元素关系）；中心单列：`WishartGamma.lean`；非中心 `1×1`：`Theorem2NoncentralScalarFormula.lean`；**`2×1`：`Theorem1TwoRowsActualCDF.lean : theorem2TwoRowsCandidate_eq_actualCDF`**（+ 中心分支）；**`3×1` 单列非中心任意均值方向：`Theorem2ThreeRowsActualCDF.lean : theorem2ThreeRowsOneColumnCandidate_eq_actualCDF`**（`λ>0,x≥0,‖encodedMean‖²=2λ`）；直接 Frobenius 参数推论：`Theorem12ThreeRowsFrobeniusCDF.lean : theorem2ThreeRowsOneColumnCandidate_eq_actualCDF_frobenius`；单列任意行仅公式侧：`Theorem2SingleColumnAnyRows.lean` | 陈述✅ 基础设施✅ 模型→公式：`2×1` 任意均值✅ / `3×1` 任意均值方向✅ / 一般❌；公式→结论同范围；审查❌ | 仅已闭合的单列与 `3×1` 单列特例；多列和一般 `(s,t,L)` 仍未证；Theorem 1 同类换元/Fubini 标 `[需人工审查]`；原文行列式模长记号仍 `[待核实]` |
| **Theorem 3** 第 `k` 个特征值 CDF 递推 | `2≤k≤s`, `x>0`；`λ₁>⋯>λ_L>0` 为非中心矩阵正互异非零特征值（(25) 有 Vandermonde 分母） | `S∼W_s(t,I_s,Ω)`，有序特征值 `φ₁>⋯>φ_s>0` | (23) `F_{φ_k}(x)=F_{φ_{k−1}}(x)+p`；`p` 是 `φ_s<⋯<x<φ_{k−1}<⋯<φ₁` 的概率。 (24) `p=c₃Σ₁detΘ(x)`，系数及分块行矩阵由 (25)–(26) 给出（arXiv:cs/0611007v2，印刷页 7） | `PaperStatements.lean : orderedEigenvalueLaw_kthCDFRecurrence_strict`（抽象 1-based 第 `k` 大事件递推，假设阈值无原子）；**真实模型无条件版：`ThresholdNoAtom.lean : paperModel_kthCDFRecurrence_strict`**；`T3FixedCardinalityRowSelection.lean : coeff_det_rowAffinePolynomial_eq_fixedCardRowSum`；`T3PaperThetaSpecialization.lean : theorem3ThetaDetSum_eq_polynomialCoefficient`（Ψ、Ξ、Θ 及已修正为分母 `Γ_{s-L}(s-L)` 的 `c₃` 代数编码）；退化单列见 `OneColumnCDFRecurrence.lean` | 陈述🔶（(23) 抽象事件递推✅，(24)–(26) 代数表达式✅）基础设施✅ 模型→公式❌ 公式→结论❌ 审查❌ | 论文 Θ 行混合和已证明等于 `det(Ξ+XΨ)` 指定系数；尚未证明 `c₃ΣdetΘ` 等于概率 `p`。特别 `c₁→c₃` 的列归一化发现了未解释的 factorial 因子，正在对抗审计；联合谱密度 (52)–(55)、Appendix C 有序域拆分/Fubini 也未形式化。真实谱简根/阈值无原子仍未连接此模型。重复 `λ` 时 (25) 分母为零，已显式限制正互异谱输入 |
| **Theorem 4** 小阈值渐近（密度最低次幂 `dₖ=(s-k+1)(t-k+1)-1`，CDF 最低次幂 `(s-k+1)(t-k+1)`） | 小 `x` / 高 SNR 主导项 | 同上 | CDF 首项 + 分集阶数 | 分集阶数算术：`PaperStatements.lean`（纯算术✅）；`1×1` 任意非中心：`ScalarNoncentralSmallX.lean` + `ScalarNoncentralSmallXLimit.lean`；**中心单列任意 `t=m`：`T4CentralOneColumnAnyRows.lean : centralOneColumnSmallestCDF_div_tendsto_factorial`**，实际 `F(x)/x^m→1/m!`；**非中心 `2×1` 任意复均值：`TwoRowSmallOutageAsymptotic.lean : noncentralTwoRowCDF_div_tendsto_exp_neg_noncentrality_half_anyMean`** | 陈述🔶 基础设施🔶 模型→公式：中心单列任意 `t`✅ / 非中心 `1×1`✅ / 非中心 `2×1`✅ / 一般❌；公式→结论同范围；审查❌ | 已证明任意中心单列硬边系数和指数，以及 `2×1` 非中心系数；一般 `s>1` 的 Vandermonde/谱相互作用、一般非中心矩阵因子、密度到 CDF 极限积分交换与 SER 引申仍未做；尺度映射标 `[需人工审查]` |
| 推论：Rice 因子单调性（式 (45)） | `K>0`, `n=st` | 确定性 | `(K+1)^n exp(-Kn)` 在 `K>0` 严格递减 | `JinWishartFormalization.lean : riceFactor_strictAntiOn`（+ 导数负） | 陈述✅ 基础设施✅ 模型→公式✅ 公式→结论✅ 审查✅（确定性论证，无测度论） | 无 |
| 推论：分集阶数 / 最弱模最小 SNR | 等功率、非负缩放 | 确定性 | 分集阶数 `(s-k+1)(t-k+1)`；最弱模 SNR 最小 | `PaperStatements.lean : DiversityOrderClaim`（算术✅）；`JinWishartFormalization.lean : weakest_mode_has_smallest_snr` | 陈述✅ 基础设施✅ 模型→公式✅ 公式→结论✅ 审查✅ | 概率侧（ outage=第 r 模 CDF ）见下一行 |
| 推论：等功率 outage / SER | 等功率、`r` 个模、完美 CSI | 多列 Wishart 最小特征模 | outage = 第 `r` 特征值 CDF；平均 SER 核 | `MIMOPerformance.lean`（弱/严格事件换算✅，零原子引理✅）；`MIMOWishartSER.lean`（平均 Q 减量 = CDF 补函数加权积分✅）；**论文式 (42)–(44) 的 `2×1,s=1,t=2,r=1` 物理 outage 特例：`PaperSingleStreamTwoRowOutage.lean`**；无原子性：单列✅（`OneColumnNoAtom.lean`）/ 多列❌ | 陈述✅ 基础设施🔶 模型→公式：抽象核✅ / 论文 `2×1` outage✅ / 一般❌ 公式→结论🔶 审查❌ | `2×1` 已闭合物理缩放、Rice 参数及高 SNR 系数；多列最小特征值无原子性未证，通用 SER/多流 outage 与论文一般参数域仍未闭合 |

## Python 侧（infoq）能力边界 —— R1 同步（S 负责，2026-09-27 后核验）

```text
[infoq 能力边界]
- infoq.check 四态：PROVED（精确有理证书，在所给约束下的无条件证明）/
  NOT_IDENTIFIED（已证不在 Shannon 锥内，≠命题为假；Ingleton、Zhang-Yeung 1998
  属预期此类）/ UNVERIFIED（LP 数值可行但证书复核失败，只是数值证据）/
  SOLVER_ERROR（求解器未正常结束）。
- 约束：马尔可夫链 "X-Y-Z"（自动展开成对条件独立）；一般等式 "I(X;Z|Y) = 0"。
- 语法：H(X,Y)、H(X|Y,Z)、I(X;Y)、I(X1,X2;Y|Z)；标量倍乘 *（可省略）、
  分数系数；禁止信息量相乘与非零常数项。
- 数值预言机 infoq.Oracle：随机采样 + Nelder-Mead 精修；输出 gap /
  counterexample / tight。纪律：反例=构造性否定；紧性=路线提示；
  都不是证明；紧而不等的假命题数值上可能漏检。
- 测试：tests/ 五文件，静态 101 个用例（协调者实跑数以 unittest 输出为准）。
- 边界：Shannon 锥只覆盖元素不等式组合；非 Shannon 型命题、测度论步骤、
  极限交换超出 LP 能力，必须人工/其他工具。数值证据永不冒充证明。
```

## 未闭合缺口清单（按优先级）

1. **G1 ✅（谱可测范围）** 论文小侧 `s×s` Gram 的有序特征值向量可测性现已闭合：实对称有限维 Courant–Fischer min-max
   已在 `IndexedCourantFischerProof.lean` 证明；复 Hermitian/RCLike Weyl 扰动界在
   `WeylComplexHermitian.lean : abs_eigenvalue_sub_le_operatorNorm_rclike`；同文件的
   `orderedHermitianEigenvalueCoordinatesContinuous` 证明 Hermitian 有序特征值坐标 Lipschitz
   连续；`PaperSmallSideGram.lean` 定义 `Fin (min m n)` 上的实际小侧 Gram，证明 shifted
   Gaussian 样本到 PSD 矩阵的可测性；主 facade 的
   `measurable_paperSmallSideSampleEigenvalueVector` 再组合谱坐标连续性，直接给出论文小侧
   整组有序谱的可测性。旧 `measurable_complexNoncentralSampleEigenvalueVector` 仍表示
   `XᴴX` 的 `n` 维谱；两种 Gram 非零特征值多重集对应关系尚未证，但不影响小侧随机矩阵的
   直接定义/可测性。此卡仅关闭确定性模型→随机变量的谱可测桥，不包括重根零测、联合密度或
   论文 CDF 闭式。
2. **G2** 非中心 Wishart 全部有序特征值联合密度及测度变换（奇异值分解/Jacobian、酉群
   积分、重根零测）仍未闭合。`RepeatedRootNullSets.lean` 证明一元实多项式零点集
   零测及绝对连续测度推论；`MvPolynomialZeroSetNull.lean : mvPolynomial_zeroSet_volume_eq_zero`
   证明任意有限维实非零多项式零点集零测；**`WishartSimpleSpectrum.lean`（S，2026-09-27
   晚新增并接入 facade）把重根零测推广到任意维度 d 的实矩阵：特征多项式有重实根的
   d×d 实矩阵集合 Lebesgue 零测。技术路线是 resultant（`resultant_map_map` 函子性）
   + 对角见证矩阵的可分性（`separable_prod_X_sub_C_iff`），绕开了 mathlib 判别式引理
   只覆盖 2/3 次的缺口；它推广了 `MvPolynomialGramTwoByTwo.lean` 的 2×2 原型。**
   **复 Hermitian 情形已闭合（2026-09-28，`ComplexGramSimpleSpectrum.lean`，已接入 facade）：**
   在 `2mn` 个实坐标的复系数多项式环上构造通用样本矩阵及其 Gram，取特征多项式与导数的
   resultant；证明复系数非零多元多项式的实零点集零测（`complexMvPolynomial_realZeroSet_volume_eq_zero`），
   用对角见证均值证明 resultant 非零，再经平移与 Gaussian 绝对连续得到
   `paperSmallSideGram_eigenvalues_strictAnti_ae`：**任意 `m×n`、任意确定性复均值 `M`，论文小侧
   `s=min(m,n)` Gram 的有序特征值几乎必然严格递减 `φ₁>⋯>φ_s`**（另有 `XᴴX`、`n≤m` 版本
   `complexSample_shiftedGram_eigenvalues_injective_ae`）。`#print axioms` 仅 propext/Classical.choice/Quot.sound。
   这闭合了 Theorem 3 递推的阈值严格/弱事件替换所需"谱简根"前提的随机矩阵侧；**阈值无原子
   已闭合（2026-09-28，`ThresholdNoAtom.lean`）**：`paperModelEigenvalue_atom_eq_zero` 证明任意固定
   `x` 下每个有序特征值无原子；`paperModelLaw` 把真实模型实例化为 `Paper.OrderedEigenvalueLaw`；
   `paperModel_kthCDFRecurrence_strict` 使论文式 (22) 在真实模型上无条件成立。
   尚未闭合：多元 Gaussian 密度桥、谱 Jacobian/联合密度。这仍是 Theorem 1–3 一般维度模型等式前置的大缺口。
3. **G3** 一般维度 Theorem 1–3 的概率等式：仅公式侧约化（单列任意行）。
4. **G4** 一般 Theorem 4 / SER / outage 封闭：`T4DensityToCDF.lean : density_to_cdf_hardEdge`
   已抽象证明若密度为 `u^d g(u)` 且 `g(u)→a`，则 CDF 积分首项系数为 `a/(d+1)`；中心单列任意行数、
   `SixDimensionalAngularBesselI2.lean` 证明 S⁵ 轴向核的 I₂ 级数积分，`SphereSixDAxialMeasure.lean`
   又证明 `toSphere` 测度上的指数核角图公式；`NoncentralSixDimensionalRadial.lean` 把轴向六维高斯
   球壳核等同于 Nuttall `(3,2)` 被积核除以振幅平方，且已证核非负、可测与中心参数总质量 `1`；
   `ThreeRowSampleCoordinates.lean` 已证明对任意复 `3×1` 均值，真实最小 Gram 特征值弱 CDF
   等于以均值实振幅为参数的有限半径径向级数积分；
   中心单列任意行数、非中心 `1×1`、非中心 `2×1` 的实际首项也已证。一般 Wishart 多列非中心密度的首项展开/系数、
   可积性及极限交换尚未给出，因此一般 Theorem 4 与通用 SER/outage 仍未完成。
5. **人工测度审查**：`2×1` 闭环（M2/M3/M4）的全部 Fubini/换元/参数对应项。
6. **记号核对** `[待核实]`：论文行列式记号 vs Lean 复行列式取模长；论文
   `Ω`/散射尺度 `ε` 与 Lean 单位方差约定的参数映射。

## 维护规则

- 每张任务卡（B0/P1/P2/L*/M*/G*/R1）完成时更新对应行；只用经构建证明的事实，
  公式侧、候选密度、真实概率律、论文定理四级分开记录。
- 本表由 C 拥有最终核验权；S 只同步 Python 侧与只读复查结论。
- 引用不确定一律 `[待核实]`；不得以"基本完成"等模糊措辞关闭任何行。
