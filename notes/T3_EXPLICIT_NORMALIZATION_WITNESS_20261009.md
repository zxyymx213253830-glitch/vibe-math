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

## 截止前原文版本检查（13:23–13:25 UTC）

实际打开 [arXiv 记录](https://arxiv.org/abs/cs/0611007)，公开修订记录仅显示
2006-11-02 v1 和 2006-11-03 v2；未见后续 arXiv 修订，不等于没有期刊更正。
重新核对 [v2 HTML T3 (23)–(26)](https://arxiv.org/html/cs/0611007v2)：
`c3` 分母只有 `Gamma_(s-L)(s-L)` 和活跃谱 Vandermonde；行选择为原顺序中的
`k-1` 个 Psi 行和其余 Xi 行。现有源转录与这一版本对应。

定向检索题名加 correction/erratum 未找到可验证的更正条目，检索结果噪声较大，
不据此声称不存在勘误。定位到 [2008 刊版候选 PDF](https://citeseerx.ist.psu.edu/document?doi=80825fb7644297a038a5ee724eca1c6f65648405&repid=rep1&type=pdf)，
但实际全文读取先超时再返回 403；[出版 DOI](https://doi.org/10.1109/TCOMM.2008.060115)
也不可访问。因此没有完成刊版公式视觉核对，不能拿搜索摘录替代该验收。
PDF 技能要求看完整相关页，这一步因来源访问受限仍 [需人工审查]。

## 用户新指令后的检索辅助闭合

用户随后提供董彬 AI4M 指南并要求继续。使用 LeanSearch 实际检索并核对本地
`Finset.powersetCard_one` 后，`T3CentralNormalizationClosure.lean` 已用结构化
`powersetCard` 改写完成通用候选到两项的等式，以及该具体候选实部大于 1 的证明。
此前三次失败的记录保留为历史；没有在旧计时窗口后偷偷延长工作。
详细验证、工具版本/使用边界见 `AI4M_GUIDE_TOOL_USE_20261009.md`。
