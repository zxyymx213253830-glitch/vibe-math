# 金石博士阶段非中心 Wishart 特征值论文：内容与 Lean 路线

## 文献定位

- Shi Jin, Matthew R. McKay, Xiqi Gao, Iain B. Collings,
  “MIMO Multichannel Beamforming: SER and Outage Using New Eigenvalue
  Distributions of Complex Noncentral Wishart Matrices.”
- 预印本于 2006-11-02 提交：<https://arxiv.org/abs/cs/0611007>。
- 期刊版发表于 *IEEE Transactions on Communications*, 56(3), 424–434,
  2008；后来获 2011 IEEE Stephen O. Rice Prize Paper Award。
- 东南大学官方履历记载金石于 2007 年 6 月取得博士学位，因此预印本属于其
  博士在读阶段。官方现职为东南大学副校长，而非校长。

## 论文解决的问题

论文研究 Rice 衰落下的 MIMO 多信道波束赋形。信道矩阵含确定性均值，因而
`H Hᴴ` 或 `Hᴴ H` 服从复非中心 Wishart 分布；各有序特征值就是各空间特征模的
增益。已有结果对任意秩非中心参数下单个有序特征值的分布不够直接，论文首先
补上这套分布公式，再把它们用于符号错误率（SER）和中断概率分析。

设 `s = min(n,m)`、`t = max(n,m)`，并按
`φ₁ > φ₂ > ... > φₛ > 0` 排列非零特征值。在完美收发端信道状态信息和
特征模传输下，第 `k` 个子信道的瞬时 SNR 与 `φₖ pₖ` 成正比。

## 主要结果

1. **最小特征值（Theorem 1）**：CDF 写为一个由 Nuttall Q 函数和上不完全
   Gamma 函数组成的矩阵行列式比值。
2. **最大特征值（Theorem 2）**：CDF 同样写成行列式比值，矩阵元素改用
   Nuttall Q 的差与下不完全 Gamma 函数。
3. **任意第 `k` 个特征值（Theorem 3）**：利用最大/最小两端的积分块，对
   有序特征值 CDF 给出递推式。这样不必直接计算高维积分。
4. **零点附近渐近（Theorem 4）**：第 `k` 个特征值密度的最低次幂为
   `dₖ = (s-k+1)(t-k+1)-1`，所以 CDF 的最低次幂为
   `(s-k+1)(t-k+1)`。

这些分布结果导出两个通信结论：

- 第 `k` 个特征模的分集阶数是 `(s-k+1)(t-k+1)`；使用前 `r` 个模时，最弱的
  第 `r` 模决定高 SNR 下的整体误差阶。
- 等功率且使用 `r` 个模时，中断概率可直接写成第 `r` 特征值 CDF。在单模、
  低中断概率的主导项中，Rice 因子依赖为
  `(K+1)^(st) exp(-Kst)`；论文式 (45) 表明它在 `K>0` 时严格递减。

论文以 `3×5` Rice 信道和 100,000 次 Monte Carlo 仿真核对分析曲线。其主要
贡献不是一种新的波束赋形算法，而是为性能分析提供了任意秩非中心情形下的
有序特征值分布工具。

## 假设与边界

- 信道是空间白化的复矩阵高斯模型，Rice 均值矩阵允许任意秩；不同的空间相关
  模型不直接包含在公式中。
- 波束赋形依赖完美 CSI；等功率中断结论不能自动外推到一般功率分配。
- 渐近公式描述高 SNR 或小阈值主导项，不是所有 SNR 上的精确替代。
- 从密度渐近到平均 SER 的极限/积分交换属于 `[需人工审查]` 的测度论步骤。

## Lean 试验结果

已在 `theory/jin_wishart_formalization/` 建立可独立构建的 Lean 4 + mathlib
项目，且不使用 `sorry` 或额外公理。除确定性论证外，当前还定义了中央/非中心
复 Wishart 概率测度：从 `2mn` 个标准实 Gaussian 坐标构造单位方差圆对称复
Gaussian 矩阵，再对 Gram 映射取推前。Lean 已证明此构造是概率测度且其质量为
1 集中在半正定锥上。它还不包括 Lebesgue 密度或论文的特征值分布公式。

目前通过机器检查的内容是：

| 命题 | 状态 |
|---|---|
| Rice 主导因子的导数（论文式 (45)） | Lean 已证明 |
| `K>0` 时该导数为负 | Lean 已证明 |
| Rice 主导因子在 `(0,+∞)` 上严格递减 | Lean 已证明 |
| 有限维复 Gram 能量非负 | Lean 已证明 |
| 等功率、非负缩放下最弱有序模具有最小 SNR | Lean 已证明 |
| 中央/非中心复 Wishart 测度定义及概率性 | Lean 已证明 |
| 复 Wishart Gram 输出几乎必然半正定 | Lean 已证明 |
| Theorem 1–3 的非中心 Wishart 特征值 CDF | 尚未形式化 |
| Theorem 4 的渐近展开及 SER 积分传递 | 尚未形式化；`[需人工审查]` |

mathlib 已有有限维实 Gaussian 测度、矩阵正半定和谱理论；本项目已用这些基础
定义出单位协方差复 Wishart 推前测度。mathlib 当前没有命名的 Wishart、Nuttall Q
和复多元 Gamma 库，也缺少论文中的矩阵变量特殊函数接口。

## 建议的完整形式化路径

1. **确定性矩阵层**：用 Hermitian/线性算子接口建立 Gram 正半定、特征值排序、
   奇异值与 Gram 特征值的平方关系。
2. **概率模型层**：定义复矩阵高斯与非中心 Wishart 随机矩阵，证明所用随机
   特征值可测。此层的可测性细节标记 `[需人工审查]`。
3. **密度与特殊函数层**：先形式化论文依赖的联合特征值密度，再定义 Nuttall Q
   和相关不完全 Gamma 积分，证明行列式积分恒等式。
4. **性能层**：从 CDF 推出 SER 与中断概率；最后处理零点渐近、积分交换和分集
   阶。所有 Fubini、支配收敛和极限交换步骤在完成前均标记 `[需人工审查]`。

因此，“用 Lean 形式化”是可行的，但合理目标应先是核心定理的最小可复用概率
库，而不是直接逐页翻译整篇论文。

## 来源

- 论文预印本：<https://arxiv.org/abs/cs/0611007>
- 论文 PDF：<https://arxiv.org/pdf/cs/0611007>
- 东南大学中文官方履历：
  <https://www.seu.edu.cn/2021/0714/c28449a378109/page.htm>
- 东南大学英文官方履历与代表作：
  <https://oic.seu.edu.cn/oicenglish/2026/0522/c68505a568520/page.htm>
