# 两列 Gram 最小模型：固定方向的实际残差能量与联合律

工作窗口 2026-10-10 01:18–02:18（Asia/Shanghai）。本卡接续已验收的
GaussianComplexOrthogonalResidual，不重复证明径向积分或 Gaussian 独立性。

## 起手检索与精确复用

实际使用 verification/leansearch_lookup.ps1，top-2 查询：

1. `Probability measures on real numbers with equal cumulative distribution function are equal`。
   命中 `MeasureTheory.Measure.cdf_eq_iff`：对实数上两概率测度 μ、ν，
   `cdf μ = cdf ν ↔ μ = ν`。本地同文件直接采用其正向引理
   `MeasureTheory.Measure.eq_of_cdf (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
   [IsProbabilityMeasure ν] (h : cdf μ = cdf ν) : μ = ν`。
   精确声明 Mathlib/Probability/CDF.lean:116–123。
   另一个候选 StieltjesFunction.measure.congr_simp 不需要：概率测度唯一性直接适用。
2. `Norm of vector supported at one coordinate in Euclidean space`。
   命中 EuclideanSpace.norm_single / nnnorm_single；在当前版本它们为弃用别名，
   回归采用现有 PiLp.single 范数 simp 接口，不复制新单坐标范数证明。

本地锁定 Lean v4.35.0-rc2、mathlib e18afff334217588afc719a8b707b00d90521064，
许可证 Apache 2.0。线上检索只提供候选，本地声明与内核才决定采用。
既有 `cdf_complexGaussianEnergy_eq_expMeasure` 直接复用；不重新造径向分布库。

另实际调用 LeanExplore 公开接口查询 `Measure.eq_of_cdf`，top-1 返回完整精确声明，
线上源码 aae61ae084c21995ee248964a81e3750ad0db2db，类型与本地锁定声明一致。
top-2 withDensity 仅为密度测度定义，与本子目标无关，不采用。

## 精确数学目标

令 a∈ℂ² 为固定单位向量，b=(-conj(a₁),conj(a₀))，Z 为独立于此固定选择的
实际单位复方差 Gaussian 列（由四个标准实 Gaussian 除以 sqrt(2) 编码）。

- ||b||=||a||，Rₐ(z)=z-<a,z>a=<b,z>b。
- ||Rₐ(z)||²=|<b,z>|²。
- 实际 ||Rₐ(Z)||² 的推前测度等于 Exp(1)。
- 实际 (<a,Z>, ||Rₐ(Z)||²) 的推前等于单位复方差标量 Gaussian × Exp(1)。

最后一条复用已验收的投影/残差能量独立及实际 Gaussian 投影 law，
不是定义残差分布为指数测度，也没有待证密度假设。
这是两列 Bartlett/Gram 条件坐标的一个真实依赖，非又一个单列 CDF 展示。

## 数值、实现与验收

本卡起手重跑 experiments/complex_gaussian_residual_control.py，退出码 0。
种子 2026100950，m=2,3,5 各 200000 样本；已知联合 Fourier/Laplace 变换
exp(-|t|²/4)(1+s)^(-(m-1)) 对照最大偏差 1.014、.964、1.725 SE。
正交误差 <1.34e-15，能量分解误差 <1.1e-14。数值不是证明。

休息前草稿首次编译发现共轭表示 `star`/`starRingEnd` 不一致，以及复合 map
重写表达式不匹配。本卡保留同一数学证明，采用 simp only 的明确共轭正规化、
显式可测函数类型与 calc 推前组合，不弱化陈述、不改 Gaussian 方差。

最终验证（2026-10-09 17:41 UTC 前）：

- `lake env lean -j1 JinWishartFormalization/ComplexTwoRowResidualEnergy.lean` 退出码 0。
- 接入 facade 后 `lake build JinWishartFormalization --quiet` 主构建退出码 0。
- `lake env lean -j1 checks/ComplexTwoRowResidualEnergy.lean` 退出码 0：具体单坐标单位
  方向的实际 Exp(1) law、完整联合乘积律及两正交投影能量分解，三个回归通过。
- 七条 public theorem 的公理均只有 propext / Classical.choice / Quot.sound。
- 新模块与检查无 sorry/admit/native_decide/新公理，git diff --check 退出码 0。

保持单线程、未改 lockfile、未启用付费服务、未推送 GitHub。

## 补库价值与最小缺口

本地可复用实际复 Gaussian 正交残差的低维指数 law 及联合概率接口；
可用于复回归、二列 QR、Schur 补及随机矩阵条件核。属于本地组合/模型桥，
不声称全球首创、已被上游接收或一般 Wishart 密度已完成。

仍缺：首列随机单位方向的可测构造与乘积积分桥、首列零事件处理、
一般行数残差 Gamma law、Gram 联合密度及其谱 Jacobian/角积分。
T1–4 的一般多列概率公式未闭合；T3 原刊归一化与边界审查另待完成。
[需人工审查] 共轭 convention、方差、推前测度与论文模型对应。
不同模型家族 P4 未完成，不称审查通过。

下一张有界卡建议：构造 `a(u)=actualComplexColumn(u)/||actualComplexColumn(u)||`，
零向量时取具体单坐标单位方向，证明整个选择可测且处处单位。
用现有 MeasurePreserving.skew_product 及本卡的逐纤维常值联合 law，
证明“首列 × (投影,残差能量)”的实际乘积律，再接回 twoColumnSplit。
这样不需要假定随机方向独立于首列，也不需要先假设首列非零几乎处处。
这仅是下一卡路线，尚未写成或验收新定理。
