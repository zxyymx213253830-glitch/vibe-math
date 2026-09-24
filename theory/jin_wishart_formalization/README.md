# 金石等（2008）论文 Lean 形式化可行性原型

目标论文：Shi Jin, Matthew R. McKay, Xiqi Gao, Iain B. Collings,
“MIMO Multichannel Beamforming: SER and Outage Using New Eigenvalue
Distributions of Complex Noncentral Wishart Matrices,” IEEE Transactions on
Communications 56(3), 424–434, 2008；预印本 arXiv:cs/0611007（2006）。

## 当前形式化范围

`JinWishartFormalization.lean` 选择论文中三个可与随机矩阵密度公式分离的骨架：

1. 式 (45) 中 Rice 因子项的导数、导数在 `K > 0` 时为负，以及该因子在
   `(0, +∞)` 上严格递减；
2. Gram/Wishart 矩阵正半定性的坐标能量形式；
3. 等功率条件下，最弱有序特征模具有最小 SNR 的序关系。

这些定理用于验证 Lean/mathlib 对论文外围确定性论证的覆盖能力，不等同于形式化
论文的 Theorem 1–4。

`JinWishartFormalization/WishartProbability.lean` 补上了概率模型基础：

- 复样本矩阵由 `2mn` 个独立标准实 Gaussian 坐标构造，实部和虚部除以 `sqrt 2`，
  因而采用单位方差的圆对称复 Gaussian 约定；另有实数版本作为对照。
- 中央与非中心 Wishart 被定义为标准 Gaussian 样本经 `Xᴴ X` 的推前测度。
- Lean 已证明这些测度是概率测度、均值坐标嵌入正确，并且输出矩阵以概率 1
  落在半正定锥中。
- 利用 mathlib 的 Hermitian 谱定理，已证明中央及非中央复 Gram 样本的降序特征值
  均非负；谱库提供的 `eigenvalues₀` 本身是 antitone（即降序）排列。
- Wishart 的最小特征值尾事件已编码为 `{W | W - xI` 半正定`}`，并证明该事件可测，
  且阈值 `x=0` 时的概率为 1。另已形式化谱定理桥梁：对 Hermitian `W`，该事件等价于
  每个特征值都不小于 `x`；在非零维度下，也等价于降序列表 `eigenvalues₀` 末项（最小
  特征值）不小于 `x`。从尾概率到论文 CDF 所需的无原子性仍待证明。
- 最大特征值一侧也已完成对应的确定性桥梁：`xI-W` 半正定等价于每个特征值不超过
  `x`，在非零维度下等价于降序列表首项（最大特征值）不超过 `x`；该事件可测，并已
  定义其非中心 Wishart 概率作为 CDF 基础。尚未证明这一概率等于论文 Theorem 2 的行列式。
- `MIMOPerformance.lean` 已形式化一般实值统计量在正 SNR 缩放下的 outage 阈值换算：
  弱事件 `cφ≤γ` 精确等于在阈值 `γ/c` 处的 CDF；严格事件 `cφ<γ` 单独保留，不能在
  未证无原子性时替换为弱 CDF。它尚未与 Wishart 的随机特征值映射接通。
- `Theorem1Formula.lean` 已将论文式 (15)–(18) 的 `Ψ(x)` 分段条目和行列式比值编码为
  Lean 定义。它只是精确的公式侧候选值；尚未证明分母非零，也尚未证明它等于上述
  Wishart 尾概率的补数。Theorem 2 的 `Ξ(x)` 条目及式 (19) 的行列式候选值也已编码；
  对应的概率等式同样未证明。
- 已证明 Theorem 1–2 公式之间的逐元素关系 `Ξ(x) + Ψ(x) = Ψ(0)`；对非中心列，
  还在核尾可积这一显式前提下，将 `Q(0)-Q(√(2x))` 改写成有限区间积分。该可积性
  目前仍未从论文参数推出。另需注意：论文的竖线记号表示行列式，而 Lean 候选式目前
  对复行列式取模长；还需证明相关行列式为实且非负，才能确认两种写法一致。
  另有 `OrderedPositiveNoncentralSpectrum` 及 `...OfSpectrum` 入口，把
  `λ₁ > ··· > λ_L > 0` 编码为结构字段；较底层的 raw 函数仍接受任意实数列，不能单独
  视作论文陈述。即便经 validated 入口，分母非零与候选式等于概率仍未证明。
- 已处理 Theorem 1 的中心标量特例 `s=1, L=0`：形式化了归一化行列式为
  `(t-1)!`、其非零性，以及 `x≥0` 时候选 CDF 化为归一化的整数 Gamma 有限和。
  这仍是公式端的约化，尚未证明该表达式等于 `XᴴX` 的概率分布函数。

这是一项实质性的概率模型和有序谱基础形式化，但还没有得到 Wishart 的 Lebesgue
密度或联合特征值密度；Theorem 1 的公式侧已编码，但还没有 CDF 等式证明，Theorem 2–4
亦未完成。当前 covariance 设为单位阵，尚未覆盖论文中的一般尺度矩阵 `Σ`。特征值现在
是逐样本的确定性结论，尚未证明对应特征值映射的可测性，也尚未从 Wishart 推前测度
得到其分布函数。

## 搜索到的可复用 Lean 库

当前项目锁定的 mathlib 已提供：

- [`Mathlib.Probability.Distributions.Gaussian.Multivariate`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Multivariate.html)：
  有限维实 Euclidean 空间上的 `stdGaussian`、`multivariateGaussian`，概率性、坐标
  协方差和特征函数定理。复 Gaussian 条目由独立实坐标对构造。
- [`Mathlib.Analysis.Matrix.PosDef`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/PosDef.html)
  与 [`Mathlib.Analysis.Matrix.Order`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Order.html)：
  Hermitian/正半定矩阵及其谱性质；`Xᴴ X` 正半定可直接调用库定理。
- [`Mathlib.Analysis.InnerProductSpace.Spectrum`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Spectrum.html)
  和 [`Mathlib.Analysis.InnerProductSpace.SingularValues`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/SingularValues.html)：
  有序自伴特征值、奇异值及二者平方关系，可作为后续随机特征值层的确定性底座。
- 普通 Gamma 函数以及积分定义的 `Complex.partialGamma` 已在 mathlib 中；但没有
  本文所需的 Nuttall `Q`、修改 Bessel `I`、复多元 Gamma 或矩阵变量超几何函数接口。
- 新增的 `IncompleteGamma.lean` 用 mathlib 的完整/下不完全 Gamma 定义其代数补函数，
  并已证明对 `x ≥ 0` 它等于 `∫ x..∞` 的上尾积分；shape-one 基值、递推和正整数
  形状闭式 `k! * exp(-x) * Σ_{j=0}^k x^j/j!` 均通过 Lean 检查。
- mathlib 也有标量 Bessel `J` 与普通/正则化超几何函数；它们并不直接给出论文中的
  Nuttall `Q` 或矩阵变量超几何函数。需要逐项构造所需函数并证明其积分/级数性质，
  而不是仅因存在相近名称就视为已覆盖。
- `NuttallQ.lean` 已以 `I_q(z)=(-i)^q J_q(iz)` 构造非负整数阶修改 Bessel `I`，
  利用整数阶 Bessel `J` 的解析性证明 `I_q` 与 Nuttall Q 核连续，定义论文对应的
  Nuttall Q 积分，并在明确的可积性前提下证明尾积分拆分恒等式。
  目前还没有证明该核对论文所需参数必然可积、非负或实值；这些性质仍是定理 1–2
  的关键待完成部分。

本次网络和已锁定 mathlib 源码检索没有找到可直接依赖的 Lean Wishart、Nuttall `Q`
或复矩阵变量分布库。因此本项目采用“复用 Gaussian + 矩阵基础库，再在本仓库
补建 Wishart 层”的路线，而非引入一个并不存在的现成 Wishart 包。

## 尚未形式化的论文核心

- 复矩阵 Gaussian 密度，以及一般协方差尺度下非中心 Wishart 的密度表示；
- 一般协方差尺度 `Σ` 下的非中心 Wishart 定义与线性变换定理；
- Hermitian 随机矩阵有序特征值的联合可测性和联合密度；
- Wishart 最小特征值分布的连续性/无原子性；
- 矩阵变量超几何函数和复多元 Gamma 函数；自建 Nuttall Q 的参数可积性/实值/非负性；
- Theorem 1–2 的候选行列式公式与 Wishart CDF 的等式证明，以及 Theorem 3 的行列式 CDF；
- Theorem 4 的小特征值渐近展开以及从渐近展开到 SER/中断概率的积分交换。

上述内容涉及测度论、特殊函数与极限交换，完整证明中的相关步骤均应标记
`[需人工审查]`，直至相应库和证明补齐。

## 构建

在本目录运行：

```powershell
$env:ELAN_HOME = 'D:\vibe math\.tools\elan'
& 'D:\vibe math\.tools\elan\bin\lake.exe' update
& 'D:\vibe math\.tools\elan\bin\lake.exe' exe cache get
& 'D:\vibe math\.tools\elan\bin\lake.exe' build
```
