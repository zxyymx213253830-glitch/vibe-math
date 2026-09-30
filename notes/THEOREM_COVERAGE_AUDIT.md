# 论文形式化覆盖审计（2026-09-28）

本审计只核对仓库现有材料和 Lean 声明；本轮没有运行 Lake，也没有重新验证构建。论文定位及方程编号依据仓库已有的 `notes/jin_2006_wishart_summary.md`、`notes/JIN_WISHART_THEOREM_TRACKER.md`、`notes/JIN_WISHART_EXECUTION_PLAN.md`，以及它们引用的官方 arXiv v2：[cs/0611007](https://arxiv.org/pdf/cs/0611007)。工作区未检索到论文 PDF 文件，因此下文的逐式对应沿用这些仓库记录；精确假设、记号和印刷页仍以原文复核为准 `[待人工核实]`。

## 状态口径

- **实际模型定理**：左边确实是项目所定义的移位复高斯样本/Gram 随机变量的概率或 CDF，结论在陈述假设下已被 Lean 证明。
- **公式侧 / 抽象桥**：证明候选函数的代数性质，或证明满足给定接口的任意概率律的性质；它本身不等于论文的 Wishart 结果。
- **局部特例**：实际模型定理，但只覆盖特定维数、中心分支或参数范围。
- **未覆盖**：论文一般维数、一般秩或相应模型—公式桥缺失。

“源文件存在”与“主入口已构建”不是本轮验证结论；除特别说明外，本审计仅按 Lean theorem 的类型判定数学覆盖。所有换元、球面参数化、Fubini/Tonelli 和极限交换仍按仓库规程标 `[需人工审查]`。

## Theorem 1：最小有序特征值 CDF（原文式 (15)–(18)）

| 层次 | 仓库已有结果 | 覆盖判断 |
|---|---|---|
| 公式侧 | `Theorem1Formula.lean` 定义 `theorem1CdfCandidate`、`theorem1PsiMatrix` 等一般参数行列式候选；含中心单列化简及矩阵/标量代数引理。`Theorem1SingleColumnAnyRows.lean` 给出非中心单列公式候选到 Nuttall-Q 比值的约化。 | **不是**一般 Wishart CDF 定理；一般维数、秩下公式候选尚未与实际模型相等。候选内部用复行列式模长，和原文记号的完全对应仍需逐式核对。 |
| 实际模型：中心 | `WishartGamma.lean`：任意正行数的中心 `m×1` 复 Wishart 唯一特征值服从 Gamma 律，并连接 Theorem 1 的中心单列候选。 | 已证明的真实模型单列中心特例，不覆盖多列。 |
| 实际模型：非中心 | `ScalarNoncentralTheorem1.lean : noncentralScalarCDF_eq_theorem1Candidate`（`1×1`）；`Theorem1TwoRowsActualCDF.lean : theorem1TwoRowsCandidate_eq_actualCDF`（非零复均值 `2×1`，另有 `L=0` 中心分支）；`Theorem1ThreeRowsActualCDF.lean : theorem1ThreeRowsOneColumnCandidate_eq_actualCDF`（`3×1`，`λ>0`、`x≥0` 且 `‖encodedMean‖²=2λ`）。 | 这些是实际 CDF 与候选公式相等的真定理，但仅为单列、低行数特例。`3×1` 陈述含显式参数匹配；不能据此声称所有 `3×1`/一般矩阵参数形式均已无条件封闭。 |
| 一般论文结论 | `PaperStatements.Theorem1Claim` 只把任意抽象 `OrderedEigenvalueLaw` 的最小值 CDF 与候选等同写成命题定义。 | 契约没有证明；抽象 law 也未自动实例化为一般 Wishart law。多列、一般 `(s,t,L)` 仍未完成。 |

## Theorem 2：最大有序特征值 CDF（原文式 (19)–(20)）

| 层次 | 仓库已有结果 | 覆盖判断 |
|---|---|---|
| 公式侧 | `Theorem1Formula.lean` 定义 `theorem2CdfCandidate`、`theorem2XiMatrix`，并证明 `Ξ(x)+Ψ(x)=Ψ(0)` 等互补代数恒等式；`Theorem2SingleColumnAnyRows.lean` 化为 Nuttall-Q 增量。 | 公式结构已编码，尚非一般最大特征值分布证明。 |
| 实际模型 | `Theorem1TwoRowsActualCDF.lean : theorem2TwoRowsCandidate_eq_actualCDF`（非零均值 `2×1`，另有中心分支）；`Theorem2ThreeRowsActualCDF.lean : theorem2ThreeRowsOneColumnCandidate_eq_actualCDF`（`3×1` 单列非中心参数匹配）。单列唯一特征值使最大值和最小值相同。 | 与 T1 同为少数单列实际模型特例；一般多列/一般维数缺模型—公式桥。 |
| 一般论文结论 | `PaperStatements.Theorem2Claim` 是抽象 law 上的候选等式定义。 | 未证明的契约，不可计为 T2 完成。 |

## Theorem 3：第 k 个特征值 CDF 递推与行列式增量（原文式 (22)–(26)）

| 子结论 | 仓库已有结果 | 覆盖判断 |
|---|---|---|
| 事件递推 | `OrderedEigenvalueCDFRecurrence.lean : orderedPair_sublevelMass_eq_add` 证明有序统计量的下水平集分解；`ThresholdNoAtom.lean : paperModel_kthCDFRecurrence_strict` 将其用于实际小侧 Gram 特征值，并用固定阈值无原子把非严格分区改为严格分区。 | 论文 (22) 的实际事件层递推已覆盖一般有限维模型；这是 T3 的真实进展，但尚未评估递增项的闭式。 |
| 行列式/系数代数 | `T3FixedCardinalityRowSelection.lean : coeff_det_rowAffinePolynomial_eq_fixedCardRowSum`；`T3PaperThetaSpecialization.lean : theorem3ThetaDetSum_eq_polynomialCoefficient`，并定义 `theorem3C3` 与 `theorem3IncrementCandidate`。 | 已证明 Θ 行混合和是相应行仿射行列式的指定多项式系数，即 (23)–(25) 的公式侧代数骨架；未证明它等于实际分区概率 `p`。 |
| 概率密度桥 | `WishartSimpleSpectrum.lean`、`ComplexGramSimpleSpectrum.lean`、`ThresholdNoAtom.lean` 给出实/复多项式零集、实际简单谱及阈值无原子相关基础设施。 | 尚无从实际矩阵高斯 law 到一般有序特征值联合密度的谱 Jacobian / 归一化推导；也没有 Appendix III 中联合密度分块积分、换序及 Fubini 证明，因此 `p = c₃ Σ det Θ` 未建立。 |
| 重要规范风险 | `notes/T3_C1_C3_normalization_audit.md` 和 `T3NormalizationAudit.lean` 记录：按目前读取的 Appendix A 常数与列积分缩放，`c₁∏dⱼ` 与显示的 `c₃` 还差 `Γ_{s-L}(t-L)`。 | 这是公式源与附录归一化之间尚未解释的因子；不是已证明的论文错误，也不是可忽略的小细节。须先对照原文 (24)–(26)、(64)–(69) 和现有 Θ 约定裁决，之后才适合 formalize 概率等式。原文页码/编号对应有 `[待人工核实]`。 |
| 声明层 | `PaperStatements.orderedEigenvalueLaw_kthCDFRecurrence_strict` 是抽象递推定理（有阈值无原子假设）。`PaperStatements.Theorem3Claim` 只要求存在一个函数 `F`，在选定的 `k,1,s` 三个位置取对应 CDF 值。 | 后者没有表达原文 (22) 的递推，更没有 (23)–(26) 的 `p`、系数或 Θ/Ψ/Ξ 公式；不能当作 T3 定理契约已对齐。 |

## Theorem 4：小阈值密度/CDF 首项与分集阶数（原文式 (27)–(34)）

| 层次 | 仓库已有结果 | 覆盖判断 |
|---|---|---|
| 算术指数 | `PaperStatements.theorem4_powers_related`、`diversityOrder_*` 证明密度幂次 `dₖ=(s-k+1)(t-k+1)-1` 与 CDF 幂次/分集阶数的算术关系。 | 只证明指数的整数代数，不证明任何特征值分布具有该渐近。 |
| 抽象分析桥 | `T4DensityToCDF.lean : density_to_cdf_hardEdge`：若密度可写成 `u^d g(u)` 且 `g` 在零点右连续趋于 `a`，则积分 CDF 首项为 `a/(d+1)`。 | 分析引理有一般形式；其密度分解、右极限和可积性尚须由实际 Wishart law 供给。 |
| 实际模型特例 | `ScalarNoncentralSmallX.lean` + `ScalarNoncentralSmallXLimit.lean` 给非中心 `1×1` 小阈值首项；`T4CentralOneColumnAnyRows.lean : centralOneColumnSmallestCDF_div_tendsto_factorial` 给中心 `m×1` 的 `F(x)/x^m→1/m!`；`TwoRowSmallOutageAsymptotic.lean : noncentralTwoRowCDF_div_tendsto_exp_neg_noncentrality_half_anyMean` 给任意复均值 `2×1` 的 `F(x)/x²→(1/2)e^{-‖M‖²/2}`。 | 这些是 CDF 渐近的真实模型结论，分别限于所列单列/中心/两行特例。它们不是论文一般 `s,t,k,L` 的 T4 公式。 |
| 性能尺度 | `ScalarNoncentralOutageAsymptotic.lean`、`T4CentralOneColumnHighScale.lean`、`TwoRowOutageScaling.lean`、`PaperSingleStreamTwoRowOutage.lean` 有若干由小阈值到高尺度的确定性缩放及单流特例。 | 不等于一般特征值密度一阶展开；物理尺度与论文 `ε,K,p_k` 映射需按具体定理单独核验。 |
| 声明层 | `PaperStatements.Theorem4Claim` 只表达抽象 law 的 `F(x)/x^d→c>0` 存在性。 | 未给原文明确首项常数/非中心参数依赖，也没有一般实际模型证明；契约与原文 T4 的完整参数化不等价。 |

## 性能公式：SER 与 outage（原文式 (35)–(45)）

| 结论 | 仓库已有结果 | 覆盖判断 |
|---|---|---|
| SER / Q 层积分 | `GaussianQ.lean` 定义标准 `Q` 与变换核；`MIMOWishartSER.lean : noncentralGram_meanGaussianQDecrement_eq_cdfComplementIntegral` 对实际移位 Gram 最小特征值证明 `E[Q(0)-Q(√(2βλ_min))]` 等于 CDF 补函数核积分；`MIMOWishartSERExact.lean : noncentralGram_BPSK_SER_add_cdfComplementIntegral` 进一步给出实际 BPSK `Q` 平均与该积分之和为 `1/2`。 | 是真实样本模型的标量 Q/CDF 层恒等式（ENNReal 积分形式）；不包含论文一般调制参数 `α,β`、活动模选择/整体 SER 界或多流/性能闭式，也未把 CDF 替换成 T1/T2 行列式。因而不能说原文 (35)–(36) 已完整形式化。 |
| outage 阈值换算 | `MIMOPerformance.lean : weakOutageProbability_eq_statisticCDF` 证明正尺度下的事件重标定，并分开处理严格/弱阈值及无原子条件。`PaperSingleStreamTwoRowOutage.lean` 将纸面 `K, ε, H̄` 映到实际 `2×1` 模型并给单流高 SNR 结果。 | 一般抽象阈值恒等式 + `2×1` 单流实际特例；不覆盖任意 `r` 多流和一般有序最小 active 模。 |
| 抽象声明 | `PaperStatements.OutageClaim` 允许 `scale*power=0`，但右侧含除以该乘积；证明 `outage_threshold_rescaling` 实际另需 `hprod : scale*power≠0`。`SERClaim` 只断言存在一个实数 `avgSER` 等于用任意非负 kernel 写出的积分。 | 这些契约有域/内容缺口：outage 需正乘积假设或单独零尺度分支；SER 契约没有将 `avgSER` 定义为实际模型的期望，也没有固定 Gaussian-Q 与论文常数，因此目前不是原文性能定理的精确接口。 |
| Rice 因子 | `JinWishartFormalization.lean : riceFactor_strictAntiOn`（及导数引理）证明 `(K+1)^(st)e^{-Kst}` 在正参数区间严格递减。 | 确定性微积分结论已形式化；仍依赖 T4 主导系数与物理参数的正确对应，不能代替一般 outage 渐近。 |

## 论文前置引理与基础设施状态

- `WishartProbability.lean` 定义由标准实 Gaussian 坐标构造的复移位 Gaussian 样本与 Gram 推前概率 law，并证明概率性及半正定性。它**没有**给出一般 Lebesgue 矩阵密度或特征值联合密度。
- `PaperSmallSideGram.lean`、`WeylComplexHermitian.lean`、`ComplexGramSimpleSpectrum.lean`、`ThresholdNoAtom.lean` 提供实际小侧 Gram、有序谱可测/连续、几乎处处简单谱及固定阈值无原子等基础结果。它们解决随机变量和事件的合法性，不推出 CDF 行列式公式。
- 一般非中心复 Wishart 有序谱的联合密度、谱变换 Jacobian、酉群积分/矩阵特殊函数积分及归一化仍缺失；这同时阻塞一般 T1/T2 的模型—公式桥和 T3 增量闭式。
- README/执行计划中已明确“编译通过”不等于“论文完成”；此审计不重新验证最近一次全工程构建或无占位扫描。

## 覆盖结论与建议的下一块

覆盖边界概括：**完整覆盖的是一些定义/代数结构、T3 的实际事件递推、性能阈值重标定等基础引理；实际模型—论文公式的闭环目前集中于非中心 `1×1`、任意均值 `2×1` 和参数匹配的 `3×1` 单列 T1/T2，以及 T4 的中心单列/非中心 `1×1`、`2×1` 小阈值特例。一般非中心多列 T1/T2、T3 概率行列式式、一般 T4、通用多流 SER/outage 仍未完成。** `PaperStatements.lean` 中几项命题是接口/契约，不应列入论文结果“已证明”。

最有价值的下一张 bounded card 是 **T3 常数归一化裁决**：在写任何 (23)–(25) 的 actual probability bridge 前，逐行对照仓库已有 arXiv v2 来源与 `T3NormalizationAudit.lean`，明确 `Γ_{s-L}(t-L)` 的额外因子是论文写法遗漏、变量/列缩放中有隐含因子，还是当前 Θ 定义未按原文正规化；完成后只更新独立的代数 theorem/审计记录，并在最小例 `s=3,t=4,L=1` 上精确核验。其依赖是原文 equation mapping 的人工复查，不依赖新增概率基础设施。

该裁决通过后，下一张概率卡建议从 **T3 的最小多特征值实际例**入手：先固定小侧 `s=2`、简单非中心谱与 `k=2`，从实际 Wishart 模型证明阈值分区增量概率等于相应 Ψ/Ξ/Θ 闭式；前置为源归一化裁决及一个真实联合谱密度/积分桥。这个例子直接检验当前最严重的模型—公式缺口，而不是再扩展已经较多的纯代数接口。

两项都只是建议任务，不表示此审计已运行证明或通过构建。
