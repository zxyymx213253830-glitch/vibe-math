# 信息论、概率论和 Lean：与论文直接连接的基础建设

日期：2026-10-16。把用户的 EAN 按 Lean 理解。本文件同时提供基础解释、现成机检入口和后续研究验收条件，不另开无关的数学支线。

## 1. 先掌握同一个随机对象的三种表达

在概率空间上，随机变量是可测映射 X；它的分布是 `Measure.map X μ`。CDF 是分布在 `Iic x` 的质量。密度是相对于指定参考测度的 Radon–Nikodym 表示。

因此“给出一个非负、积分为1的函数”和“证明实际 X 具有这个密度”是两件事。本文从实际样本出发，证明推前等于 `withDensity`，不把待证密度写进前提。

Lean 阅读入口：`WishartProbability`、`TwoRowActualDensity`、`TwoRowMinimumLaw`。重点读 `Measure.map_map`、`Measure.map_apply`、`withDensity_congr_ae` 的全部假设。练习：沿着实际 Gram 密度证明，列出每个映射的源空间、目标空间和参考测度，检查是否在正确实维上积分。

## 2. 连续 Gaussian 的单位与独立性

两个独立 N(0,1) 经 `(U+iV)/sqrt 2` 组成单位复方差 CN(0,1)，其复范数平方均值为1。实坐标 stdGaussian 的半范数平方在实维2k时服从 Gamma(k,rate=1)。振幅乘a，能量乘a²；“方差a”和“振幅a”不可互换。

联合 Gaussian 的不同正交投影因交叉协方差为零而独立。单独知道两个边缘变量是 Gaussian 并不够，必须有联合 Gaussian 假设。

现成机检入口：`stdGaussian_orthogonalProjectionOnto_law`、`stdGaussian_orthogonal_split_indep`、`stdGaussian_orthogonal_split_law`、`stdGaussian_projected_half_norm_sq_law`。这些复用 mathlib 的 Gaussian 理论。练习：解释为什么把固定 K 替换成由先前随机列生成的 K(z)，不能直接调用固定子空间乘积律。

## 3. 从概率到信息论应用，要区分事件与编码定理

对非负增益g、rho>0，定义数学统计量 `log(1+rho*g)`，单位为nats。严格的事件等价是

`log(1+rho*g) <= R  <->  g <= (exp R-1)/rho`。

本次已形式化通用等价及实际中心2×2最弱模式中断公式。R<0时事件为空，R=0时概率为0，R≥0时调用实际CDF。若目标用bits，先转换为 `R*log 2`。

这里证明的是一个指定统计量的概率律。要把它称为某个系统的可达速率/容量，还需声明Gaussian输入、噪声、接收端CSI、模式功率分配等模型并连接信息量定义。总MIMO互信息是模式速率之和，不能用最小模式速率替代。

近期高价值基础任务：把“可测非负增益的单调速率事件”抽成可复用接口，并把物理信道假设与数学随机增益分层。暂不为这篇稿件声称已经形式化 Shannon 编码定理。

信息不等式基础仍可使用本仓库 infoq：离散熵上的数据处理、条件互信息非负和链式法则适合精确LP证书。该工具的 Shannon 锥计算不验证连续 Gaussian 密度或 Wishart Jacobian；不要跨语义使用。

## 4. Lean 阅读与证明的最短实践路径

依次读定义、精确陈述、证明依赖，而不是只看文件名或 tactic 是否成功。

1. `log_one_add_mul_le_iff`：把非线性函数的事件先转为实数不等式。识别 `rho>0` 和 `gain>=0` 在哪里使用。
2. `actualTwoRow_weakestLogRate_outage`：用集合外延性证明事件相等，再调用已证实际CDF。不要重新积分。
3. `actualTwoRow_minimum_CDF`：理解严格尾事件的补集恰是弱CDF，无需凭直觉互换严格/弱不等式。
4. `actualTwoRow_minimum_law_expTwo`：从所有阈值的CDF一致识别完整概率测度。
5. `stdGaussian_orthogonal_split_law`：理解联合分布、独立和两个边缘分布怎样组合成乘积律。

每个练习的交付是精确声明、假设清单、已有资产定位和内核检查；不以复制大量 tactic 作为理解证明的替代。引用锁定mathlib源码，避免根据最新版网页猜API。

推荐官方材料：[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)；概率核背景：[Degenne, Markov kernels in Mathlib's probability library](https://arxiv.org/abs/2510.04070)；换元基础：[Gouëzel, 2022](https://arxiv.org/abs/2207.12742)；通信背景：[Tse与Viswanath的作者页面](https://stanford.edu/~dntse/wireless_book.html)。具体课程练习不假称已完成。

## 5. 学术价值最高的后续研究，按依赖推进

| 优先级 | 精确任务 | 验收条件 | 不能替代它的工作 |
|---|---|---|---|
| P0 | 完成论文语义审查与可复现发布 | 独立审查记录、哈希对应的证明和稿件、公开固定版本 | 再增加孤立低维公式 |
| P1 | 从固定投影律到参数化随机投影律 | 显式可测参数、纤维律/概率核、实际联合分布；处理异常集 | 把随机子空间直接代入固定K定理 |
| P2 | 一般实坐标Cholesky一步Jacobian | 任意s的导数块结构与绝对行列式 r^(s-1)，域和逆映射 | 只做s=2,3,4符号计算 |
| P3 | 实际中心矩阵密度归纳 | 从Gaussian样本推导密度、常数递推、边界零测 | 新增待证密度假设hDensity |
| P4 | 中心一般最小值锥积分与可计算结果 | 调用真实矩阵密度；t>s保留det(V+xI)^(t-s) | 擅自把方阵的指数律推广到长方阵 |

一般非中心G2及原T3概率桥另列长期任务。T3在来源和常数解释未裁决前不做概率桥。

所有新概率猜想先以固定种子、已知控制数值筛查；LP仅用于可表达的离散信息不等式。数值通过仍不是证明。所有新测度/条件化/换元步骤 `[需人工审查]`。

这份安排不需要论文等待一般G2完成。当前稿件的范围先封闭；新的通用基础形成后，再判断是否值得单独写成后续研究。
