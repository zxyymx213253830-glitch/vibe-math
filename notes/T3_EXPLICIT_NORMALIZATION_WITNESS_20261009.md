# T3 两个显式行选择的严格归一化见证（2026-10-09）

## 已证对象，不扩大结论

对当前源对齐的 `Psi/Xi/Theta` 定义，取 `s=2,t=3,L=0,k=2,x=2`。
`T3CentralNormalizationWitness.lean` 使用两个显式行集合 `{0}`、`{1}`，证明

`re(det Theta_{0} + det Theta_{1}) = 16 exp(-2) - 28 exp(-2)^2 > 1`。

上/下不完全 Gamma 条目都由已有机检整数形状公式求值，指数上下界直接复用
mathlib `Real.exp_one_gt_two` / `Real.exp_one_lt_three`；不是采样或浮点验证。
显示标量 `c3=1` 有独立回归检查，因此这两个具体项的和不能直接作为概率。
已有固定种子实际 `3×2` 样本数值控制在先，见 `T3_SCALAR_SOURCE_ALIGNMENT_20261009.md`。

**范围边界：** 未声称当前 `theorem3IncrementCandidate` 已整体判假，也未声称正式
期刊定理有误。两个显式项与通用 powerset 求和 API 的等式尚未在此卡证明；
来源版本、排列/隐含归一化、最终刊版和勘误仍 [需人工审查]。
这卡不是新的联合谱密度或完整 T3 概率定理。

## 三次失败与保留状态

通用 powerset 求和到两项的展开三次尝试停在有限和化简：
1. `Fin.univ_two` 在锁定版本不存在；
2. 重写 `univ={0,1}` 后 `powerset_insert` 留下 union/image；
3. 明确四个子集后默认 simp 仍留下三项 insert 有限和。

依任务书停止该子目标，不继续随机添加 tactic。最小缺口是证明在
`Fin 2` 的 powerset 上，只取基数 1 的和等于 `{0}`、`{1}` 两项。
保留已闭合的 Gamma 条目、显式两行列式及严格指数不等式。
未来可使用已证通用固定基数/系数接口处理，但本轮没有将它冒充完成。

## 补库/复用价值

本地新增的可复用内容是源公式具体常数的精确回归方法：整数 Gamma 闭式、
有限维行列式及已证指数界组合。它可防止“代数恒等式构建绿色但常数错误”。
这不声称新数学结果、全球首创或 mathlib 上游贡献。

## 验收

直接文件编译和 `lake build JinWishartFormalization.T3CentralNormalizationWitness --quiet`
退出码 0；主工程 `lake build JinWishartFormalization --quiet` 退出码 0。
两个公共定理公理仅 `propext / Classical.choice / Quot.sound`。
`lake env lean -j1 checks/T3CentralNormalizationWitness.lean` 包含严格界与 `c3=1`
回归，退出码 0。`git diff --check` 无空白错误，源码无证明占位或新公理。
无独立跨模型家族审查，不称审查通过。
