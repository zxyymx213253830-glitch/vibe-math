# 截止前有界检索：Bartlett 联合密度的现成组件

2026-10-10 02:13–02:17（Asia/Shanghai）最后有界卡，仅检索及核对精确类型。
不新增 Lean 证明、不声称坐标联合密度已验收；此前7035112主构建和审计仍为最后验证状态。

## 实际工具查询与排除

运行 verification/leansearch_lookup.ps1，每条top-2：

- `Product of measures with densities has density the product of the component densities`
  命中 MeasureTheory.prod_withDensity、prod_withDensity₀。
  本地 Mathlib/MeasureTheory/Measure/WithDensity.lean:719–728，section SFinite/Prod：
  `[SFinite μ] [SFinite ν]`、hf:Measurable f、hg:Measurable g 时，
  `(μ.withDensity f).prod (ν.withDensity g) =
  (μ.prod ν).withDensity (fun z => f z.1 * g z.2)`。
  AE版本只要求相应 AEMeasurable。两次调用可组合三边缘，不必重证Fubini密度。
- `Pushforward Gaussian measure by invertible linear map has density`
  命中 gaussianReal_map_linearMap 及一维gaussianReal_map_symm_apply。
  它们不是目标复标量密度；不拿一维结果未经坐标桥直接替代二维结论。
- `Complex Gaussian real imaginary coordinates standard normal independent`
  命中 GaussianInt.toComplex_def（高斯整数，完全不相关）和独立实Gaussian和的law。
  均不闭合目标；检索名字含Gaussian不等于概率Gaussian资产。
- 针对体积改为 `Complex real imaginary measurable equivalence preserves Lebesgue volume`，
  精确命中下面两个关键现成定理，避免再次补复实体积库。

LeanExplore查询prod_withDensity只返回withDensity定义；这是邻近定义，不是所需乘积定理，
不采用这个结果作证明。候选索引aae61ae084c21995ee248964a81e3750ad0db2db；
最终以本地锁定e18afff334217588afc719a8b707b00d90521064核对，Lean v4.35.0-rc2、Apache2。

## 已核实可直接组合的精确组件

Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean（全文核对）：

- `Complex.measurableEquivRealProd : ℂ ≃ᵐ ℝ × ℝ`，z↦(z.re,z.im)。
- `Complex.volume_preserving_equiv_real_prod :
  MeasurePreserving Complex.measurableEquivRealProd volume volume`。
- `Complex.measurableEquivPi : ℂ ≃ᵐ (Fin 2 → ℝ)`，z↦![z.re,z.im]。
- `Complex.volume_preserving_equiv_pi :
  MeasurePreserving Complex.measurableEquivPi volume volume`。

Constructions/Pi.lean:862–877的measurePreserving_finTwoArrow_vec、
volume_preserving_finTwoArrow可处理两坐标函数/乘积空间；四坐标还需明确重排。
此处不是仅连续或线性等价，已有**体积保测度**，不能重复手证其Jacobian。

本项目已验收的GaussianRawCoordinates.lean:86–90：
`stdGaussian_halfVariance_shift_eq_withDensity`，Fintype.card ι=2*k 时：
`stdGaussian(EuclideanSpace ℝ ι).map (fun z => sqrt(2)⁻¹ • z + ν) =
volume.withDensity (fun z => ofReal ((π⁻¹)^k * exp(-||z-ν||²)))`。
对k=1直接复用并用现成保范/保体积坐标桥识别复标量律，不再次径向积分。

Mathlib/Probability/Distributions/Gamma.lean:128：
`gammaMeasure a r = volume.withDensity (gammaPDF a r)`；
Exponential.lean:96：`expMeasure r = gammaMeasure 1 r`。
Gamma(2,1)和Exp(1)边缘本就定义为标准实坐标的withDensity，无需再猜归一化。

## 下一张证明卡及边界

1. 把实际复标量CN(0,1) law在上述保体积实坐标中识别为π⁻¹exp(-(x²+y²))。
2. 用两次prod_withDensity与明确四坐标重排，把已验收Bartlett联合律接为
   S*π⁻¹*exp(-(S+x²+y²+E₀))，支持S>0、E₀>0；先逐项证明尺度和边界零质量。
3. 采用7035112已验收的Jacobian=S消去S因子，再证明实际Gram坐标密度。
   不能在S=0直接除S，也不能把联合密度作为假设冒充模型结论。
4. 此后才进入Gram→有序谱的Jacobian/角积分；非中心核仍另缺。

以上只是准确定位的复用路线，**没有新联合密度定理**。本卡不改Lean源码或依赖，
无需为笔记重复5分钟主构建；最后源码构建/公理记录仍由7035112给出。
[需人工审查] 四坐标重排、volume、边界支持及论文对应；P4跨模型家族审查未完成。
没有新建检索agent、没有使用秘密/付费服务、没有推送GitHub。
