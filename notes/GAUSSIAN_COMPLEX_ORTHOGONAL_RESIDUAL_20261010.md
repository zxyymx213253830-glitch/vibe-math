# 恢复工作：实际复 Gaussian 投影与正交残差独立

工作窗口 2026-10-10 01:18–02:18（Asia/Shanghai），即
2026-10-09 17:18–18:18 UTC。本轮只验收休息交接中这一张残差卡；
二维残差能量草稿不顺便计为已完成。

## 检索优先与精确复用

恢复后实际再次调用 `verification/leanexplore_lookup.ps1`，查询
`HasGaussianLaw indepFun covariance inner`，top-1 精确命中
`ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_inner`。
声明要求 **联合** Gaussian law，以及所有交叉实内积泛函协方差为零，
结论为两个整个向量的 `IndepFun`，不是仅零相关。

线上源码版本 `aae61ae084c21995ee248964a81e3750ad0db2db`；
本地核实 mathlib `e18afff334217588afc719a8b707b00d90521064`，
Lean v4.35.0-rc2、Apache 2.0。精确声明在本地
`Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean:329`。
同时复用 `covarianceBilin_stdGaussian`、`covarianceBilin_apply_eq_cov`、
`IsGaussian.hasGaussianLaw_id`、`HasGaussianLaw.map_of_measurable`、
`IndepFun.comp`、`stdGaussian_map` 和实际推前的 `map_map`。
没有复制许可不明外部项目，也没有从头证明 Gaussian 独立性或径向积分。

## 数学陈述

对任意行数 m、任意**确定性**单位复列 a：

`R_a(z) = z - <a,z> a`。

- 残差与 a 复正交；其投影映射在实际 ℝ 内积下自伴。
- `||z||² = |<a,z>|² + ||R_a(z)||²`。
- 实际标准 Gaussian 复列下，`<a,z>` 与整个 `R_a(z)` 独立。
- 编码坐标映射保持 Gaussian law，因此 `/sqrt(2)` 的实际单位复方差列
  也满足上述独立性；投影与残差能量独立。
- 实际 `(投影, 残差)` law 等于“单位复方差标量 Gaussian law × 实际残差 law”。

最后一条的残差 law 是实际推前，不是假设其密度或定义成期望的 Gamma law。
`ha : ||a||=1` 是真实固定投影的结构假设，不是把待证联合谱密度放入假设。
证明显式构造两输出的共同线性 Gaussian 映射，不能从边缘 Gaussian alone 推独立。

## 数值与形式化验收

恢复后重跑 `complex_gaussian_residual_control.py`，退出码 0：
seed=2026100950，m=2,3,5 各 200000 样本。
对照投影能量均值 1、残差能量均值 m-1、联合 Fourier/Laplace 变换
`exp(-|t|²/4) (1+s)^(-(m-1))`。
最大对照偏差 1.014、.964、1.725 个标准误，正交与能量分解误差 <1.1e-14。
这只是实现对照，**不是**独立性或联合密度证明。

恢复首次模块构建报错：末条乘积 law 的 rewrite 规则把函数写成
`innerSL a ∘ actualComplexColumn`，目标为展开后的 `inner a (actualComplexColumn v)`。
本轮修复仅显式标注两个目标函数的可测性类型，使规则与目标一致，未改数学陈述。
随后 `lake env lean -j1 JinWishartFormalization/GaussianComplexOrthogonalResidual.lean`
退出码 0，九条结果均通过直接编译。
`lake build JinWishartFormalization --quiet` 主构建退出码 0；随后
`lake env lean -j1 checks/GaussianComplexOrthogonalResidual.lean` 退出码 0。
9 条公理审计仅 `propext / Classical.choice / Quot.sound`；
具体 3 行独立、2 行能量分解及具体非空单位方向三个回归均通过。
新模块/检查文件无 sorry、admit、native_decide、新 axiom；`git diff --check` 通过。
2026-10-09 17:29 UTC 前验收完成，主入口已导入。本卡已达到可运行状态。
本轮保留单线程，直接源码编译通过后只做一次主构建（其中包括本模块），
再运行检查文件；避免另跑成功的局部 lake 构建后又重复主构建的依赖扫描。
不因读依赖较慢就改 lockfile、降级或跳过主构建。

## 论文作用、补库价值与最小剩余缺口

该卡解除多列 Gram/Bartlett 推导里“第二列投影与残差到底是否独立”的固定方向依赖，
并支持第二个 Gram 对角项的能量分解。不是又一个单列 CDF 特例。
可复用在复回归、匹配滤波、复随机矩阵 QR 与条件 Gaussian 核。
这些是本地库组合/实际模型桥，不声称全球首创或已贡献上游。

仍需随机首列方向的可测性与迭代积分、残差能量 Gamma law、Gram 联合密度，
以及从 Hermitian 矩阵到有序谱的 Jacobian/角积分；非中心模型还需移位核。
不能把固定正交投影的独立性直接套成随机 QR 的完整分布。
T1–4 一般多列概率公式仍未完成。
`[需人工审查]` 共轭、方差、推前测度与论文模型对应；不同模型家族 P4 尚未完成。
