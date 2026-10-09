# 金石等 Wishart 形式化：可复用 Lean 工作定向检索（2026-10-09）

**主 agent 验收补记：** Andréief 已移植并在当前工具链完成模块与主入口构建，
回归及依赖公理审计通过，均退出码 0；不再是仅待移植建议。
下文保留检索时的状态。完整许可证、固定来源、改动及验证见
`ANDREIEF_REUSE_ACCEPTANCE_20261009.md`。

## 结论与边界

发现一个直接相关、值得优先移植的现成证明：`mo271/Zeta5` 的 **Andréief 行列式积分恒等式**。
它可以省掉联合谱密度建立之后的有限置换展开/Fubini/积分行列式约化，不必重写这一段。
当前锁定 mathlib 已有 Gaussian 等距不变性、零协方差推出独立、有限乘积积分、一般 Jacobian
换元和确定性 Gram–Schmidt。以下给出精确符号，优先直接调用，不另造同等功能。

本次是源码和版本/许可检索，**未在当前项目编译外部代码、未做依赖公理审计、未证明新定理**。
主 agent 已据本次发现将固定提交的 Andréief 文件移植到当前项目，并收窄导入；
本笔记完成时其编译仍待完成，本文不提前声称移植验收通过。
没有检索到可直接替换本项目 `hDensity` 的完整非中心复 Wishart **有序谱联合密度**证明。
这只限定在下述搜索范围；不表示全球不存在此类形式化。

已阅读 `AGENTS.md`、`T4_NONCENTRAL_ONE_COLUMN_ANY_ROWS.md`、`THEOREM_COVERAGE_AUDIT.md`。
本次没有触碰现有证明、依赖配置或主 agent 新模块，唯一新增文件是本笔记。

## 1. 最优先：外部 Andréief 证明，可单文件移植

来源：[mo271/Zeta5 / Apery/Andreief.lean](https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Andreief.lean)。
检索时 `main` 提交为 `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`；原文件 109 行，
唯一导入为 `import Mathlib`，无需为这一个结果引入整个 Zeta5 项目。

精确定理名 `Apery.andreief`：

```text
μ : Measure ℝ, [SigmaFinite μ]
f g : Fin n → ℝ → ℝ
hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ
⇒ det(∫ f_i g_j dμ) = (1/n!) ∫ det(f_i(x_j)) det(g_i(x_j)) dμ^n.
```

辅助可复用符号：`Apery.permEquiv`、`Apery.measurePreserving_permEquiv`、
`Apery.integral_prod_prod_eq`。源码实际包含置换保测度、逐项可积性、有限和移入积分及
置换计数，不只是把恒等式当公理。源码检索无 `sorry` / `axiom`；这不替代本地内核验收。

版本：[Lean v4.34.0-rc1](https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/lean-toolchain)，
[mathlib f385f9fd18abed332ebcd3df239cb357e264aceb](https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/lakefile.toml)。
许可证：[Apache 2.0](https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/LICENSE)。
当前项目 v4.35.0-rc2，不能在未编译前声称直接 import 已通过；建议保留来源/许可证及改动说明，
单文件移植，并 `#print axioms Apery.andreief`。

对主线作用：为 T1/T2 的密度积分→行列式，以及 T3 分块积分提供现成骨架。
限制：原定理实值、各坐标同一 `μ`，无有序区域假设；混合上下区间需 indicator 或有限和展开。
它**不**证明 Gaussian Gram 推前谱密度，不自动处理排序的 `n!` 因子，也不裁决论文 c3 常数。

## 2–5. 已在锁定 mathlib 中，可直接 import 的组件

以下全部以本地锁定提交 `e18afff334217588afc719a8b707b00d90521064` 为准，
已核实源码声明而非仅凭搜索摘要。工具链与本工程相同：`leanprover/lean4:v4.35.0-rc2`。
mathlib [许可证为 Apache 2.0](https://github.com/leanprover-community/mathlib4/blob/e18afff334217588afc719a8b707b00d90521064/LICENSE)。

### 2. Gaussian 固定等距变换和正交投影独立

[Mathlib/Probability/Distributions/Gaussian/Multivariate.lean](https://github.com/leanprover-community/mathlib4/blob/e18afff334217588afc719a8b707b00d90521064/Mathlib/Probability/Distributions/Gaussian/Multivariate.lean)：

- `ProbabilityTheory.stdGaussian_map`：`f : E ≃ₗᵢ[ℝ] F` 时，`(stdGaussian E).map f = stdGaussian F`。
- `ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis`：任意实正交基中标准 Gaussian
  等于独立 `gaussianReal 0 1` 坐标的推前。
- `ProbabilityTheory.map_pi_eq_stdGaussian`：普通函数乘积空间到 EuclideanSpace 的标准桥。

[Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean](https://github.com/leanprover-community/mathlib4/blob/e18afff334217588afc719a8b707b00d90521064/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean)：

- `ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_inner`。
- `ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_inner`。
- `ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_eval`。

实际覆盖：联合 Gaussian 向量族的所有交叉线性泛函协方差为零，则向量独立。
复 Gaussian 可先采用本项目已有实坐标编码；不需要重证特征函数分解。
适合固定正交投影、固定列/行分块。**随机 QR 方向依赖已采样列时，仍需条件 law/核或
对外层变量的积分桥；不能把固定投影独立直接套到随机投影。**

### 3. 有限乘积 Fubini 与置换保测度

[Mathlib/MeasureTheory/Integral/Pi.lean](https://github.com/leanprover-community/mathlib4/blob/e18afff334217588afc719a8b707b00d90521064/Mathlib/MeasureTheory/Integral/Pi.lean)：

- `MeasureTheory.integral_fintype_prod_eq_prod`。
- `MeasureTheory.Integrable.fintype_prod`（以及依赖类型版本 `fintype_prod_dep`）。

实际覆盖：对各坐标函数的积，有限乘积测度下的积分等于各坐标积分之积；
可积性另有已证接口。Andréief 文件也使用 `measurePreserving_arrowCongr'` 做坐标置换。
这些均在工程当前依赖中，避免人工再证 n 维 Fubini/置换代数。
注意 Bochner 积分对不可积函数也有默认值；概率/归一化用途仍需明确可积性条件。

### 4. 有限维注入可微换元，不是现成谱 Jacobian

[Mathlib/MeasureTheory/Function/Jacobian.lean](https://github.com/leanprover-community/mathlib4/blob/e18afff334217588afc719a8b707b00d90521064/Mathlib/MeasureTheory/Function/Jacobian.lean)：

- `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`。
- `MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`。
- `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`。
- `MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul`（OpenPartialHomeomorph 版本）。

实际覆盖：有限维实空间 `E → E`，可测域上注入，给定每点 Fréchet 导数，
积分换元乘 `|det f'|`；不要求额外重证一般换元定理。
直接用途为低维 Gram/坐标参数化，一旦建立合法坐标图即可调用。
限制：`X ↦ XᴴX` 不注入且维数下降，Hermitian 矩阵→特征值也降维；不能直接套此定理。
必须补角变量/商空间/分层局部图，证明导数行列式与 Vandermonde 因子，并处理奇异集合。

### 5. Gram–Schmidt/QR 的确定性部分

[Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean](https://github.com/leanprover-community/mathlib4/blob/e18afff334217588afc719a8b707b00d90521064/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean)：

- `gramSchmidtNormed_orthonormal`：线性独立输入的规范 Gram–Schmidt 输出正交归一。
- `gramSchmidtOrthonormalBasis_inv_isUpperTriangular`：原输入在构造基的坐标矩阵上三角。
- `gramSchmidtOrthonormalBasis_det`：行列式等于对角投影内积之积。

这是复或实内积空间可用的确定性 QR 骨架，但**没有** Bartlett 三角随机项的分布与独立结论。
若选 QR 路线，仅补随机律桥，不重写正交化与三角代数。

## 进一步外部工作：可参考，不立即导入

### 实 Wishart / 残差投影卡方：Hansen econometrics

仓库：[mostlyharmfuleconometrics/lean-hansen-econometrics](https://github.com/mostlyharmfuleconometrics/lean-hansen-econometrics)。
检索时 [lean-toolchain](https://github.com/mostlyharmfuleconometrics/lean-hansen-econometrics/blob/main/lean-toolchain)
为 `v4.29.0`。GitHub 仓库 metadata 的 license 为空，递归树未见顶层 LICENSE；
**代码复用许可证 [待核实]，不能当作已许可直接复制。** 未核验其锁定 mathlib 提交或本地构建。

[HansenEconometrics/ChiSquared.lean](https://github.com/mostlyharmfuleconometrics/lean-hansen-econometrics/blob/main/HansenEconometrics/ChiSquared.lean)：

- `HansenEconometrics.hasLaw_quadForm_symmIdem_chiSquared_fintype`：实际标准实 Gaussian `Z`，
  固定实 Hermitian 幂等矩阵 `M`，`0 < M.rank`，则 `ZᵀMZ` 为自由度 `M.rank` 的卡方。
- `HansenEconometrics.hasLaw_stdGaussian_normSq_chiSquared_fintype`。

[Chapter11MultivariateRegression/MatrixNormal.lean](https://github.com/mostlyharmfuleconometrics/lean-hansen-econometrics/blob/main/HansenEconometrics/Chapter11MultivariateRegression/MatrixNormal.lean)：

- `sampleContrastRows_iIndepFun_of_orthogonal_iid_normal_rows`：独立同分布 Gaussian 行，
  固定 `C*Cᵀ=1` 的行混合后仍独立。
- `standardCoordinate_schurComplement_eq_residualProjection`。
- `gaussianResidualProjection_isHermitian`、`gaussianResidualProjection_idempotent`、`gaussianResidualProjection_rank`。

检查的两个文件源码未命中 `sorry` / `axiom`；未检查全部传递依赖，不称其整体无公理。
此处是真实实 Gaussian 二次型/投影 law，但不是复非中心有序谱联合密度。
`wishartMatrixLaw` 本身是 Gram 推前定义，不能因文件出现 Wishart 一词就说已有所需密度。
版本迁移、复杂依赖与许可风险使其优先级低于当前 mathlib 原生接口；先借证明结构。

### 两个随机矩阵项目的范围排除

- [FredRaj3/SemicircleLaw](https://github.com/FredRaj3/SemicircleLaw)：Lean v4.24.0，MIT。
  `SemicircleLaw/EmpiricalMeasure/EigenvalueContinuity.lean` 有
  `EigenvalueContinuity.continuous_eigenvalueMap` / `measurable_eigenvalueMap`；
  与本仓库已有谱基础重叠。实际读取主文件
  `SemicircleLaw/WignerSemicircleLaw/WignerSemicircleLaw.lean`，`RandomMatrix.wigner_semicircle_law`
  仍含 `sorry`，不能把主定理作为已证结果引入。目标是 Wigner 矩方法，不是 Wishart 密度。
- [Lean-MoDS/StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib)：Lean v4.34.0，Apache 2.0。
  检查递归树和 `Probability/RandomMatrix/Basic.lean`、`Bernstein.lean`；
  `RMT.matrixSingularValue_sq_bounds_of_sampleCovarianceDeviationOperatorNorm_le` 等为
  实随机矩阵奇异值/样本协方差浓缩界，不是精确复谱 law。不能用尾界替代论文等式。

## Haar、特殊函数及现有内容避免重复

锁定 mathlib 的 `MeasureTheory/Measure/Haar/Basic.lean` 和 `Unique.lean` 有 Haar 构造及
`Measure.haarMeasure_unique`、`Measure.isHaarMeasure_eq_of_isProbabilityMeasure` 等一般接口。
它们不包含本任务所需的酉群角积分求值。搜索 `Wishart`、`Nuttall`、`Andreief`、`Andréief`、
`Itzykson`、`Harish.Chandra`、`Bartlett`、非中心 chi/Gamma 等词在当前 Mathlib 源码未命中。
`HaarToSphere.measurePreserving_homeomorphUnitSphereProd` 是球面/半径测度桥；
不是谱分解的商空间换元公式。

`ProbabilityTheory.gammaMeasure` / `cdf_gammaMeasure_eq_integral` 与
`Matrix.IsHermitian.spectral_theorem` / `det_eq_prod_eigenvalues` / `trace_eq_sum_eigenvalues`
已在锁定 mathlib，项目也已有相关应用。无须再做同级重复封装。

## 建议下一步（不等同于完成）

1. 先把外部 Andréief 单文件移植、在当前版本构建并审计公理；引用版本和 Apache2.0 保留。
2. 在已知/候选谱密度的积分层使用它，独立核验排序阶乘与中心归一化；
   保持与实际 Gaussian 模型证明分开，不用新 `hDensity` 接口冒充模型密度已证。
3. 真模型桥先固定最小多列中心例。按选定坐标路线直接调用原生等距不变性、
   固定投影独立、一般 Jacobian；新增只集中于尚缺的维数/角变量/真实推前层。
4. [需人工审查] 可积性、奇异集、角变量测度与排序域系数。外部源码查阅不是 P4 跨家族审查。

检索方法：锁定 mathlib 全文/文件名扫描；GitHub 官方源码、递归 tree API、toolchain/许可证；
浏览查询 Lean Wishart / Andréief / Nuttall-Q / HCIZ / Bartlett，命中后仅依据实际一手源码判覆盖。
未采用 Python 数值库作为 Lean 证明，也未依据项目宣传的“0 sorries”替代源码审查。
