# 直接复用 Andréief 证明的验收（2026-10-09）

用户授权的检索 agent 找到 [mo271/Zeta5 的完整证明](https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Andreief.lean)。
主 agent 核对固定 commit 源码、Lean 工具链、Apache-2.0 许可证及根目录
无 NOTICE 后，只移植一个证明文件，不引入整个上游项目或改变 mathlib 版本。

## 对论文的实际价值

`JinWishart.Andreief.andreief` 证明对任意 `n`、SigmaFinite 实测度 `μ` 和实函数族
`f_i,g_j`，若每个 `f_i*g_j` 可积，则

```text
det(∫ f_i g_j dμ) = (1/n!) ∫ det(f_i(x_j)) det(g_i(x_j)) dμ^n.
```

这是金石论文 Appendix A/B 中联合谱密度积分约化为行列式的一段通用工具。
保测度的坐标置换、有限和移入积分、乘积 Fubini、符号及 `n!` 计数均已在上游证明，
此次直接复用并在当前版本重新内核检查。原证明不含任何 Wishart `hDensity` 假设。
不能用它宣称已证 Gaussian Gram 谱密度；有序域的 `n!`、T3 混合上下区间以及
特殊函数核的可积性仍是独立义务。

## 修改与许可

源命名空间 `Apery` 改为 `JinWishart.Andreief`；全库导入收窄为六个模块；
修改说明和出处保留在文件头。数学证明保留，不冒充本项目原创补库。
完整许可证及来源记录在 `theory/jin_wishart_formalization/third_party/`。
相比上游 v4.34.0-rc1，当前 v4.35.0-rc2 无需修改任何数学证明即可通过模块构建。

## 控制与验收

先运行 `experiments/andreief_hilbert_control.py`，固定种子 `20261009`。
对 `[0,1]` 上单项式，独立展开 Vandermonde 平方并精确积分，与 Hilbert 行列式
已知值对照：`n=2` 为 `1/12`、`n=3` 为 `1/2160`；多维积分分别为 `1/6`、`1/360`。
每维 200000 次均匀采样，最大偏差 `0.641` 个标准误。退出码 0，数值不是证明。

`lake build JinWishartFormalization.Andreief --quiet` 退出码 0。
主入口集成后 `lake build JinWishartFormalization --quiet` 退出码 0；
`lake env lean checks/Andreief.lean` 退出码 0。
`andreief` 及其置换积分辅助定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
回归证明任意维数的等价积分优先形式 `integral = n! * det(moment)`，包括 `n=0`，
直接调用移植定理，检查阶乘位置。初始常数回归会被 simp 独立化简而未真正检验
定理调用，因此替换为这一一般回归；最终无告警。新文件无占位或新增公理。

[需人工审查] 应用到论文时的可积性、谱密度及排序域对应；本次源码复用和内核
构建不替代跨模型家族审查。检索还得到当前 mathlib 的 Gaussian 等距不变性、
零协方差独立、有限乘积积分、一般 Jacobian 及确定性 QR 骨架，详见
`LEAN_WISHART_REUSE_SEARCH_20261009.md`，优先直接调用，不重造同级组件。
