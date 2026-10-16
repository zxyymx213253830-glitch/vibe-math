# P4 对抗审查回应：Wishart 形式化论文（独立深查）

- 日期：2026-10-16
- 审查人：WorkBuddy（Step 模型家族）——与证明写作者（Codex/GPT 家族 + 本地 DeepSeek-prover）不同家族，满足 AGENTS.md P4 的跨家族要求。
- 审查性质：**语义级对抗审查**（读声明、读证明体、核对模型对应与陈述自洽）。未重跑 Lean 内核；内核证据以仓库既有记录为准并已抽查。**这不是人工数学审阅的替代。**
- 审查依据：`verification/WISHART_P4_REVIEW_PACKET.md` + AGENTS.md P4 模板（只报告问题，不重写证明）。
- 前置哈希核对：`WISHART_P4_REVIEW_MANIFEST.json` 的 96 个源文件 + 稿件 main.tex 的 SHA256 **全部与当前磁盘一致**（0 处不符），审查对象即钉住版本。

---

## 0. 总结论

**在本次审查范围内（中央 2×2 主链 + 2×1/3×1 单列链 + 缩放/中断率 + 固定子空间 + T4 渐近 + Frobenius 参考测度），未发现会推翻论文主张的数学错误或隐藏假设。** 论文主链的每个概率步骤都从实际样本测度出发，没有把目标密度当前提；论文对严格/弱事件、正支撑、归一化、方差约定的处理与代码一致；稿件对未完成事项的披露与实际状态相符。

发现的问题全部是**文档精度级**（详见 §4）：没有"必须改否则不能投"的新增项；真正的投稿阻塞项仍是从属既有的三项（空署名、无公开工件、未完成人工语义审查）。

必须同时说明：**"本次范围未发现具体问题" ≠ 全面人工认可。** 见 §5 的未审查范围。

---

## 1. 前置证据抽查（先验证审查对象本身）

| 项 | 核对 | 结果 |
|---|---|---|
| 审查包哈希 | 96 源文件 + 稿件 SHA256 逐一重算 | 全部一致，无漂移 |
| 公理记录 | `verification/publication_checks/claims-axioms.txt`：119 条公开声明逐条 `#print axioms` | 全部仅依赖 `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`；稿件 §6.1 的表述准确 |
| 主链声明在场性 | 该日志含 `actualTwoRow_BartlettCoordinates_law`、`actualTwoRow_GramRealCoordinates_eq_traceDensity`、`actualTwoRow_minimum_tail`、`actualTwoRow_minimum_law_expTwo`、`theorem1CentralTwoRow_candidate_eq_actualCDF` 等头条声明 | 在列且标准三公理 |
| claims.json | `public_declaration_count=119`、`all_targets_printed_standard_axioms=true`、fresh rebuild 165 模块 PASS、`full_Lake_build: NOT_RUN` | 与稿件 §6.1 披露一致（未冒称完整 Lake 构建） |

---

## 2. 分区审查结果

### 2.1 审查包 §2：中央复 2×2 实际链（最深的一条，逐文件读过）

**样本模型**（`WishartProbability.lean`）：`complexSampleMatrix` 的 `/√2` 编码确为单位复方差（实际 CN 密度 π⁻¹e^(−‖z‖²) 由 `actualTwoRow_Complex_eq_normalizedDensity` 从 stdGaussian 换元得到，不是我方假设的密度）；均值编码满足 ‖μ‖²=2‖M‖²；`complexWishart` 定义为 Gram 推前而非密度构造。✓

**Bartlett 独立律**（`TwoRowRandomDirectionLaw.lean` + `GaussianTwoColumnIntegration.lean` + `GaussianComplexOrthogonalResidual.lean` + `ComplexTwoRowResidualEnergy.lean`）——审查包特别要求查"是否把不同变量误当独立"：
- 独立性来自 `HasGaussianLaw.indepFun_of_covariance_inner`（联合 Gaussian + 零互协方差），协方差计算显式用到残差算子的 ℝ 自伴性（已证）。是真正的联合律论证，不是变量混淆。✓
- 随机首列方向用 mathlib `MeasurePreserving.skew_product` 传输**常纤维律**（`twoRowFiberCoordinates_law` 对每个 u 包括 0 成立），没有把"随机方向独立"当假设。✓
- 零首列：`twoRowUnitDirection` 给出可测的单位方向 fallback，重构恒等式对一切 z 成立（含 0）；正支撑由实际 Gamma/Exp 边缘的 `Iic 0` 零测导出（`TwoRowBartlettSupport.lean`）。✓
- 率/方差约定：Gamma(2,1) 形状 2 率 1、Exp(1) 率 1、CN(0,1) 方差 1，与稿件一致。✓

**Gram chart 与 Jacobian**（`TwoRowGramChart.lean`、`TwoRowBartlettCoordinateVolume.lean`）：Fréchet 导数、det=s（下三角）、正域单射、`lintegral_image_eq_lintegral_abs_det_fderiv_mul` 换元、逆 Jacobian 密度接口均在；`twoRowGramChart_positive_image` 证明 {s>0,e>0} 的像恰为 D。✓

**Gram 密度**（`TwoRowActualDensity.lean`、`TwoRowActualNormalizedDensity.lean`）：π⁻¹e^(−(u+v)) on 开锥 D；归一化（质量=1）由"推前是概率测度"导出，不是密度前提；`withDensity_congr_ae` 的使用限于限制测度上，合法。✓

**谱阈值与最小值律**（`TwoRowHermitianThreshold.lean`、`TwoRowSmallestEigenvalueCDF.lean`、`TwoRowMinimumLaw.lean`）：2×2 正定判据从迹/行列式特征值公式推出（未假定谱）；`twoRowShiftedCone` 是**开**锥，与 `x < λ_min`（严格）对应；CDF 用集合补集精确得到（无需原子性转换）；负阈值经 PSD 排除；`expMeasure 2` 经 CDF 唯一性识别。与稿件定理 4.1 逐条对应。✓

**候选连接**（`Theorem1Formula.lean`、`Theorem1CentralTwoRowActualCDF.lean`）：(s,t,L)=(2,2,0) 时 Ψ(x)=e^{−x}[[x²+2x+2,x+1],[x+1,1]]、det=e^{−2x}、det Ψ(0)=1，与稿件显示式逐字一致；复行列式范数比=实行列式比的说明仅限该特例且已在稿件中限定。✓

### 2.2 审查包 §3：缩放链（`TwoRowScaledMinimum.lean`）

Gram 缩放 a² 来自实际缩放样本（`deepseek_scaled_sampleMatrix`，GUIDED 助手）；谱缩放经阈值判据传递；a>0、v>0 假设显式；振幅 a 与方差 v=a² 全文分名；事件传输未把目标密度藏进前提。与稿件推论 4.2 一致。✓

### 2.3 中断率（`TwoRowLogRateOutage.lean`）

`log_one_add_mul_le_iff` 把正性独立于任何律声明；负目标概率为 0 由点态非负得到。与稿件 remark 4.3 公式一致。✓

### 2.4 审查包 §1：2×1 链（`Theorem1TwoRowsActualCDF.lean` 及依赖）

- 事件=实坐标球（半径 √(2x)，中心 −μ）由 `NoncentralOneColumnEnergy.lean` 精确建立，四维归一化常数 (√(2π))^{−4}=(2π)^{−2} 已核。✓
- 任意非零均值：4D 球概率只依赖 ‖μ‖（`stdGaussian_fourDBall_anyMean_eq_one_sub_nuttallQ21`，声明签名含 μ≠0、R≥0，调用点均已供给）；零均值走 L=0 中央分支单独处理。✓
- 复 Nuttall-Q → 实核：`nuttallQ21_eq_realIntegral` 带显式可积性前提（`nuttallQ21Integrand_integrableOn_Ioi`），正性由核非负导出，不是未声明的"实数性/正性"假设。✓
- 参数匹配：稿件 λ = ‖complexSampleMean M‖²/2 = ‖M‖²_F。✓
- 夹逼积分（`gaussian_shiftedBall_integral_bounds`）用 `IntegrableOn`（紧集上连续），不是无条件的 Fubini。✓

### 2.5 审查包 §4：3×1 链（`Theorem1ThreeRowsActualCDF.lean` 及依赖）

(3,2) Nuttall 核 = a²×实径向核的桥梁带可积性前提；任意均值形式把参数兼容性 `‖encoded mean‖²=2λ` 作为显式假设（`theorem1ThreeRowsOneColumnCandidate_eq_actualCDF`）；零阈值 Q(0)=a² 精确成立（非仅实部）。✓

### 2.6 审查包 §5：通用路线边界

`GaussianOrthogonalProjectionLaw.lean`/`GaussianOrthogonalSplitLaw.lean`：coisometry 特征函数论证、协方差独立性，**只处理固定确定性子空间**，docstring 明说随机子空间需条件律桥梁；`GaussianTwoColumnIntegration.lean` 的 Tonelli 用 lintegral（非负核），docstring 明说避免未声明的绝对可积前提。`CentralHermitianCoordinates.lean`：n² 实坐标等价 + 坐标测度推前，未声称 Gaussian→Wishart 密度。稿件对这三者的范围限定与代码一致。✓

### 2.7 审查包 §6：参考测度（`HermitianCoordinateMetric.lean`）

坐标 Frobenius 能量恒等式（一般维数，非对角计两次）、2×2 显式框架 diag(1,1/√2,1/√2,1)（det=1/2，推前乘 2）、(2π)^{−1} 系数换参考测度均在；**显式框架推前测度 vs 内在 Frobenius 子空间体积的区分被保持**，稿件也明说后者待人工确认。✓

---

## 3. 数值与来源声明的核对

- §6.2 数值控制：seed 20261015、200000 样本、KS≈0.00238（迹-Gamma(4,1)）/0.00124（最小值-Exp(2)）、特征值公式最大偏差 <5e−15、15 组参数组合——与 `verification/WISHART_LOG_RATE_OUTAGE.json` 逐项一致。✓
- §6.3 AI 工作流计数：38=2+29+7、另 2 次手动失败不计入、5 次 P4 无有效产出——与 `notes/DEEPSEEK_CODEX_ROUND3_SUMMARY_20261011.md` 逐字一致。✓
- §6.1 工具链/mathlib/模块数：与 `lean-toolchain`、`lake-manifest.json`、状态页一致（上一轮已核，本轮确认无变化）。✓

---

## 4. 问题清单（按严重程度；只报告，不改证明）

### I-1【低】稿件对 Gram chart 定义域的描述窄于一个辅助 Lean 陈述

- 位置：稿件 §3 "Its domain is s>0, e>0, and its image is D" vs `TwoRowGramChart.lean` 的 `twoRowGramChart_lintegral_change`（定义域仅 {0<p₀}）。
- 事实：证明实际使用的 `twoRowGramChart_density_map`/`twoRowGramChart_weighted_volume_map` 定义域是 {0<p₀ ∧ 0<p₃}，与稿件一致；`twoRowGramChart_positive_image` 证明该域像恰为 D。更宽的 {p₀>0} 陈述只是一个辅助积分恒等式（其像含 D 外点，但该陈述不用于密度传递）。
- 为何内核通过不能排除：内核保证两个陈述各自为真，不保证稿件文字与每个代码陈述的域一一对应；读者对照代码时可能误以为漏条件。
- 补救义务（作者决定）：§3 可加半句"change-of-variables 在更大定义域 {s>0} 上陈述，应用于 a.s. 正的 Bartlett 支撑"。

### I-2【低】稿件主张窄于已验证的代码（保守取向，非错误）

- 位置：`Theorem1TwoRowsActualCDF.lean::theorem1TwoRowsCandidate_eq_actualCDF`、(1,2,1) 任意均值候选=实际 CDF；`Theorem1ThreeRowsActualCDF.lean::theorem1ThreeRowsOneColumnCandidate_eq_actualCDF`、(1,3,1) 同理。稿件只提 (2,2,0) 中央候选（Table 1 亦如此）。
- 为何提：审稿者对照工件会发现稿件少报了已证特例；保守本身无害，但"贡献清单不完整"是典型的审稿意见来源。
- 补救义务：作者决定是否在 §5 补一句"additional verified specializations"。

### I-3【提示·开放】一般参数 T1/T2 公式转录未逐式核对源文

- 位置：`Theorem1Formula.lean` 的 `theorem1QOrder`/`theorem1GammaIndex`/`theorem1PsiEntry`（一般 (s,t,L) 分支）。
- 本轮所做：我独立核算了 (2,2,0)、(1,2,1)、(1,3,1) 三个特例，内部自洽且与稿件显示式一致；**一般参数的 Q 阶、Gamma 指标、2^… 因子未与源文逐式比对**（无期刊全文，arXiv v2 的逐式核对按状态页记录此前做过，我未重复该比对）。
- 为何内核不能排除：内核只证明"特例候选=实际 CDF"；未实例化分支的转录错误内核无意见。
- 补救义务：保持稿件现有披露（"an equation-by-equation journal comparison is not claimed"）；今后任何一般参数 claim 之前必须先逐式核对。**这是正确的当前状态，不是缺陷。**

### I-4【提示】一般 n 弱尾/严尾并存的代码阅读风险

- 位置：`WishartProbability.lean::smallestEigenvalueTailEvent` 是**弱**事件（W−xI ≽ 0 ⟺ λ_min ≥ x）；2×2 链经**开**锥得到严格尾。
- 影响：当前稿件主张（严格尾 + 补集 CDF）不受影响，且代码 docstring 已注明"转 ≤ CDF 需无原子证明"。
- 补救义务：后续把一般 n 事件用于严格尾时，必须补无原子步（`ThresholdNoAtom.lean` 等已有资产可复用）；无需改动稿件。

### I-5【提示】§2.1 一般维数 Frobenius 体积因子是稿件推导，非 Lean 定理

- 位置：稿件 §2.1 "in dimension s, induced Frobenius volume is 2^{s(s-1)/2} times this coordinate measure"。
- 事实：机器核对的是 s=2 显式框架（`HermitianCoordinateMetric.lean`）与一般维数能量恒等式（非对角计两次）；"能量计两次 ⇒ 体积因子 2^{s(s-1)/2}" 这一步是文中标准推导，未形式化。我手算复核成立（每对非角坐标的 Frobenius 度规为 2·I₂）。
- 补救义务：无需改动（稿件未声称其已形式化）；如求严谨可加 "derived in the text" 半句。

### I-6【提示】未审查范围（明确列出，见 §5）

---

## 5. 未审查范围（本节之外不存在"未发现问题"的结论）

**读过全文的文件**（32 个）：审查包、manifest、失败审查的 request/response、claims.json、claims-axioms.txt；以及 `WishartProbability`、`TwoRowRandomDirectionLaw`、`TwoRowGramChart`、`TwoRowActualDensity`、`TwoRowActualNormalizedDensity`、`TwoRowBartlettCoordinateVolume`、`TwoRowBartlettSupport`、`TwoRowGramPositive`、`TwoRowHermitianThreshold`、`TwoRowSmallestEigenvalueCDF`、`TwoRowMinimumLaw`、`TwoRowScaledMinimum`、`TwoRowLogRateOutage`、`Theorem1Formula`、`Theorem1CentralTwoRowActualCDF`、`Theorem1TwoRowsActualCDF`、`Theorem1ThreeRowsActualCDF`、`GaussianOrthogonalProjectionLaw`、`GaussianOrthogonalSplitLaw`、`GaussianTwoColumnIntegration`、`T4NoncentralOneColumnAnyRows`、`NoncentralOneColumnEnergy`、`ComplexTwoRowResidualEnergy`、`GaussianComplexOrthogonalResidual`、`HermitianCoordinateMetric`、`CentralHermitianCoordinates`。

**只核对了声明签名（未读证明体）**：`NoncentralFourDimensionalGaussianCDF.lean`（4D 任意均值球 → Nuttall-Q）、`NoncentralThreeRowNuttallQ.lean`（3×1 任意均值 CDF 声明及下/上半质量拆分）。二者的假设均在调用点显式供给（μ≠0、R≥0、均值范数≠0）。

**未读**：其余约 130 个项目模块（含 `NuttallQ.lean`、`IncompleteGamma.lean`、`GaussianRadialLaw.lean`、`GaussianEuclideanBallDensity.lean`、`CentralWishartConeIntegral.lean`、`CentralWishartBlockStep.lean`、全部 Bessel/径向/六维模块、T3 相关模块），以及 mathlib 本身。这些有内核检查覆盖，但**无语义审查覆盖**。

**边界**：本回应是跨家族语义对抗审查，不替代人工数学审阅；内核 PASS 不等于语义验证；数值控制不是证明。稿件 §6.4 的"独立审查边界"披露在本轮之后应更新为"已进行一次跨家族语义审查（Step 家族），人工审查仍未完成"——是否更新由作者决定。

---

## 6. 给投稿决策的三句话

1. 数学与代码对应：主链干净，可投性不受数学阻碍。
2. 文档精度：I-1/I-2/I-5 都是"改了更好"，不改也不构成错误。
3. 阻塞项不变：空署名、无公开工件、未完成**人工**语义审查——本回应把"独立 P4"从"未进行"推进到"已进行一次跨家族语义审查，结论：范围内无具体问题"，但按仓库铁律，它仍然不算人工审查完成。
