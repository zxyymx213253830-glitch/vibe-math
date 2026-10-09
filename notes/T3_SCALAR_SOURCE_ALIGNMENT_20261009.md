# T3 标量常数源对齐：代码错误与原文疑点分开（2026-10-09）

## 直接目标

在建立多列实际谱密度桥前，先确保下游 T3 常数确实是所核对来源的表达式。
源为 [arXiv:cs/0611007v2 HTML](https://arxiv.org/html/cs/0611007v2)：
T3 (25)、Lemma 1 (53)–(55)、积分核 (64) 及 Appendix C。
编号用 HTML 版；旧 Lean 文档方程编号不同，不能直接据旧编号对齐。

## 已确认的本地编码错误

`T3PaperThetaSpecialization.theorem3C3` 的源码实际使用了
`numerator * (Gamma * Vandermonde)`，虽然文档和追踪表已经写成分母。
显示式 (25) 以及独立审计 `T3NormalizationAudit.paperC3` 均为除法。
本次将实际定义改为除法，并新建 `T3ScalarNormalizationBridge.lean`：

- `theorem3GammaFactor_eq_factorialMultigamma`：两套 Gamma 定义一致。
- `theorem3C3_eq_auditedScalar`：T3 候选常数与独立审计的表达式相等。
- `theorem3_densityColumnFactors_eq_derivedC3`：验证正互异谱后，密度标量常数
  乘全部列因子，等于单独定义的 `theorem3DerivedC3`。
- `theorem3DerivedC3_fullRank`：满秩没有非活跃列，派生常数与显示常数一致。

这不是新概率定理，而是修复“编译绿色但论文表达式编码错误”的问题。
已有行列式系数恒等式不依赖常数的数值，因此此前构建成功不能发现此错误。
新的数值控制和 Lean 回归必须覆盖常数的具体值，而非仅检查形状一致。

## 不默默修改的原文疑点

原有标量审计指出列因子乘积还留下 `Gamma_(s-L)(t-L)` 分母。
因此派生常数定义为 `displayed_c3 / Gamma_(s-L)(t-L)`，与显示式分开命名。
本次仅连接两套现有定义，不将派生常数宣称为真实概率的已证常数。

中心 `s=2,t=3,L=0,k=2` 的显示常数为 1，但联合谱密度中归一化为 1/2。
在原文给定未归一化 Gamma 矩阵上，显示常数乘混合行列式和可超过 1。
数值检查 `x=2` 给出约 `1.652527`；将额外 `Gamma_2(3)=2` 因子除掉后为
`0.826263`，实际复 `3×2` 样本估计为 `0.827370`。
这强烈提示当前 v2 显示公式/矩阵约定有缺项，不是已经在 Lean 中证明原文错误。
正式发表版本、可能勘误、Theta 的排列符号或隐含归一化仍须逐项核对。
**不可把原文错误当新公理，也不可通过修改前提将待证概率结论藏进去。**

## 数值控制

`experiments/t3_scalar_normalization.py`，种子 `20261009`：

- 精确有理控制：`(s,t,L)=(3,4,0)` 为 `1/2`（旧代码为 2）；
  `(4,6,1)`、谱 `[2]` 为 `1/32`（旧代码为 `1/8`）；
  `(3,5,2)`、谱 `[4,1]` 为 `1/48`（旧代码为 `3/16`）。
- SymPy 精确整数行列式核对中央全区间矩矩阵的行列式为
  `Gamma_s(s) * Gamma_s(t)`，覆盖 `s=2,3,4` 和三个 `t`。
- 200000 个实际单位复方差 `3×2` Gaussian 样本，在阈值 `1,2,3` 与
  归一化联合密度积分对照，最大偏差 `1.306` 个标准误；显示式显著不符。
- 运行退出码 0。初次脚本错误地要求空乘积的指数为整数，已修正后完整重跑通过。

不是信息量线性不等式；infoq Oracle/Shannon LP 不适用。数值不是证明。

## 验收与剩余工作

验证：数值控制退出码 0；`lake build JinWishartFormalization.T3ScalarNormalizationBridge --quiet`
退出码 0；`lake env lean checks/T3ScalarNormalizationBridge.lean` 退出码 0；
`lake build JinWishartFormalization --quiet` 退出码 0。检查打印的三个桥接定理仅依赖
`propext`、`Classical.choice`、`Quot.sound`；无新增公理或占位证明。
回归机检 `s=3,t=4,L=0` 的显示常数为 `1/2`，以及 `s=2,t=3,L=0` 的显示常数为 1、
派生常数为 `1/2`，防止两种概念以后再次混淆。

[需人工审查] 谱密度来源、Theta 行/列顺序、原文版本差异、概率到积分的换元。
跨模型家族审查未完成。下一步仍是实际多列模型的联合密度桥；本次没有新建
将 `hDensity` 当假设的概率接口，也没有声称 T3 已完成。
