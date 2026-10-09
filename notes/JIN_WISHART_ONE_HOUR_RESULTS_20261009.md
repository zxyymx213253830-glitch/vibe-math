# 金石 Wishart 一小时任务：真实成果与交接

工作窗口：2026-10-09 20:27:39–21:27:39，Asia/Shanghai。
2026-10-09 13:28:04 UTC 检查已过截止，自动任务 `automation` 已成功置为 PAUSED。
截止后仅做本次保存与汇总，没有开启新证明或实验。没有推送 GitHub 或创建 PR。

## 窗口内提交

| 提交 | 已验收成果 | 不能扩大为 |
| --- | --- | --- |
| `96764c5` | 修复 `theorem3C3` 将分母误乘的真实代码错误；连接独立标量审计，显示常数与派生常数分开 | T3 概率公式已证、源文归一化已正确 |
| `ebee4e4` | 移植有 Apache-2.0 许可证、固定版本的 Andréief 证明；一般阶乘控制与公理审计通过 | 已有 Wishart 联合谱密度 |
| `b4f1093` | 任意矩形维数、任意复均值的实际 Gaussian 整谱 law 等于移位密度推前；Borel 谱事件等于原样本空间积分，无候选 `hDensity` 前提 | 积分已换到谱空间、Gram/谱 Jacobian 已证 |
| `a29d860` | 中央 `s=2,t=3,L=0,k=2,x=2` 两个显式混合行列式和的精确表达及实部严格大于 1 | 通用 T3 候选整体已形式化判假、正式论文错误 |
| `dab74a4` | arXiv 修订与公式核查、刊版 PDF 访问失败均留下证据边界 | 未找到勘误等于没有勘误、搜索摘录等于刊版验收 |

`b58a474` 的任意行数单列 T4 CDF 渐近在工作窗口前已提交，不计入这一小时的新成果。
这一小时没有继续堆单列特例，没有处理 OFDM 或其他项目。

## 验收证据

四个代码状态各有局部验证、主工程构建和关键定理 `#print axioms`。
最新 `lake build JinWishartFormalization --quiet` 退出码 0；具体 Gaussian 谱事件、
任意维总质量、T3 明确两项严格界和 c3 回归通过。关键新定理公理仅
`propext / Classical.choice / Quot.sound`。无 `sorry/admit/native_decide` 或新公理。
早先 Windows 并行构建发生依赖读取错误和 `std::bad_alloc`，限制线程后原证明通过；
没有修改依赖版本来掩盖失败。原有不明归属未跟踪文件未删除、未提交。

固定种子 `20261009` 的数值控制分别核对：T3 精确有理常数/中央矩行列式与实际
200000 个 `3×2` 样本；Andréief 的 Hilbert 闭式与 2/3 维积分；Gaussian 平移密度
及三个矩形模型共 600000 个样本。具体偏差与命令见对应验收笔记。
数值是实现控制，不是上述 Lean 证明的依据。

## 复用和补库价值

研究 agent `lean_reuse_search` 已完成，未重复创建；报告
`LEAN_WISHART_REUSE_SEARCH_20261009.md` 已读并采用直接可用候选。
Andréief 源码来自 `mo271/Zeta5` 固定提交
`7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`，许可证/来源保留在工程 `third_party/`。
仅移植所需单文件，证明主体保留；它不是本项目首创。

公开 `map_withDensity_measurePreserving`，并补充任意有限维 Gaussian 平移完整 law
及实际整谱事件接口，直接调用既有 Gaussian 密度、谱可测性及平移保测度证明。
可用于其他有限维 Gaussian/矩阵统计模型，是本地接口补库，不声称全球首创、
不声称已被 mathlib 上游接收。T3 显式归一化见证提供精确常数回归，避免只验表达式形状。

## 当前最小缺口与接续顺序

1. **核心模型桥：** 将已证原始样本积分转成 Gram/谱和角变量积分。
   需正确实/复体积缩放、维数降低、奇异集处理、谱 Jacobian、角测度归一化。
   现有一般同维单射 Jacobian 不能直接用于不单射且降维的 Gram 映射。
2. 在合法联合谱密度之后使用已复用 Andréief，检查排序区域的阶乘及混合区间。
   然后连接一般 Theorem 1–3；目前没有完成这些概率等式。
3. T3 通用 powerset 和到 `{0}`、`{1}` 两项的 API 桥三次失败后停止，详见
   `T3_EXPLICIT_NORMALIZATION_WITNESS_20261009.md`，不继续盲试。
4. arXiv v2 已核查；刊版候选 PDF 超时/403，正式 DOI 不可访问，未完成刊版逐式核验。
   显示式与派生常数仍分开，不默默修原定理、不添加待证结论为假设。
5. 一般非中心多列 T4 及密度渐近仍未完成，不能用已证单列 CDF 渐近代替。

[需人工审查] 全部测度变换、模型/事件对应及来源版本解释。
不同模型家族独立复核未完成，未声称审查通过。

相关详细记录：`ANDREIEF_REUSE_ACCEPTANCE_20261009.md`、
`GAUSSIAN_MATRIX_SPECTRAL_INTEGRAL_20261009.md`、
`T3_SCALAR_SOURCE_ALIGNMENT_20261009.md`、
`T3_EXPLICIT_NORMALIZATION_WITNESS_20261009.md`。
