# 成果整理与论文取舍

整理日期：2026-10-16。论文主线为实际 Gaussian 样本 → Bartlett 联合律 → 四实 Gram 密度 → 正定锥平移 → 最小特征值律。

## 可进入正文的结果

| 结果 | 严格范围 | 正文位置 | 核对入口 |
|---|---|---|---|
| 实际 Bartlett 乘积律与密度 | 中心复 2×2，条目 CN(0,1)；Gamma 和 Exp 均按 rate | 第3节 | `TwoRowRandomDirectionLaw`、`TwoRowActualNormalizedDensity` |
| 实际 Gram 密度 | 四实 Hermitian 坐标，密度 π⁻¹ exp(-trace)，PD 锥支撑 | 第3节 | `actualTwoRow_GramRealCoordinates_eq_traceDensity` |
| 实际最小特征值完整律 | 中心复 2×2；严格尾 exp(-2x)，CDF 1-exp(-2x)，x≥0 | 第4节 | `actualTwoRow_minimum_law_expTwo` |
| 实际正尺度律 | 振幅 a>0、方差 v=a²；Exp(rate=2/a²) | 第4节 | `actualTwoRow_scaled_minimum_law` |
| 最弱模式对数速率中断 | log 为自然对数，a>0、rho>0，R≥0；不是总 MIMO 容量 | 第5节 | `actualTwoRow_weakestLogRate_outage` |
| 固定子空间 Gaussian 分解 | 任意有限实维，确定性子空间；投影、独立、乘积律及偶实维能量 Gamma | 第6节 | `stdGaussian_orthogonal_split_law` |
| 非中心单列首项 | 任意正行数 m、任意确定性复均值；CDF/x^m → exp(-||M||²)/m! | 第6节 | `noncentralOneColumnSmallestCDF_div_tendsto_frobenius` |

已有 1×1、2×1、3×1 的实际模型与原候选公式连接作为支撑覆盖，不把每个特例包装成一项独立主要贡献。

## 学术贡献的表述

本文不声称发现新的经典 Wishart 分布公式。可检验的贡献是：真实样本模型与这些公式之间的形式化证明链、明确的测度/尺度约定、可复用概率接口，以及逐声明的复现证据。没有完成全面优先权检索，不写“首次”。

相对 mathlib 的新增工作，应归于具体模型的编码、接口组合与证明；Gaussian 特征函数、联合 Gaussian 零协方差推出独立、一般换元定理等已有基础必须正确署源。

## 单独标记，不进入已证主定理

- 一般中心 Hermitian 坐标与候选核平移是确定性/积分资产；一般实际矩阵密度尚未建立。
- 随机子空间条件律和一般 Cholesky Jacobian 仍是核心研究卡。
- 一般非中心 G2、一般参数下原定理1–4仍开放。
- T3 当前转录候选 >1 的见证是精确结果；秩一模拟支持残留因子2是数值证据。刊版、约定或勘误未裁决，不能称“推翻/修正刊版定理”。正文将其限定为诊断案例，可在投稿前移到附录或删去。
- 独立 P4 尚未完成。所有换元、Fubini、Gaussian 方差和论文对应继续 `[需人工审查]`。

## 本次实际新增

`TwoRowLogRateOutage.lean` 四个声明已通过叶子检查，仅标准三公理。先做了 seed=20261015 的200000个实际 Gaussian 样本控制，之后证明事件与已有实际 CDF 的组合。这个结果是应用接口，不是新的容量公式或新的编码定理。

全源码重新编译发现旧 `FourRowSampleCoordinates` 引用了一个已更名的引理；修复仅将调用名对齐到已存在的 `stdGaussianEightDBall_axial_eq_radialCDF`，数学目标未变。该维护不增加本文对 4×1 原论文候选的覆盖声明。

确切源码哈希、实际重新检查状态见 `claims.json` 和 `../../verification/WISHART_PUBLICATION_REBUILD.json`。
