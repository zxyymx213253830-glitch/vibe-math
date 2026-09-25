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
  特征值）不小于 `x`。现在还定义了非中心 Gram 样本的最小有序特征值，并从移位 PSD
  阈值事件证明该随机变量可测；这不依赖一般性的特征值连续性定理。从尾概率到论文 CDF
  所需的无原子性仍待证明。严格 CDF `P(λ_min<x)` 已精确证明为 `1-` 对应 Wishart 移位
  PSD 尾事件的概率；尚缺的是把严格 `<` 换成论文使用的弱 `≤`。
- 最大特征值一侧也已完成对应的确定性桥梁：`xI-W` 半正定等价于每个特征值不超过
  `x`，在非零维度下等价于降序列表首项（最大特征值）不超过 `x`；该事件可测，并已
  定义其非中心 Wishart 概率作为 CDF 基础。尚未证明这一概率等于论文 Theorem 2 的行列式。
- `MIMOPerformance.lean` 已形式化一般实值统计量在正 SNR 缩放下的 outage 阈值换算：
  弱事件 `cφ≤γ` 精确等于在阈值 `γ/c` 处的 CDF；严格事件 `cφ<γ` 单独保留，不能在
  未证无原子性时替换为弱 CDF；另已证明若相应等值集质量为零，则严格与弱 outage 概率相等。
  Wishart 最小特征值在该层面的无原子性尚未证明。还封装了 mathlib 的 layer-cake 定理，将非负随机变量上
  `∫₀ᶠ g` 型误差核期望改写为尾概率加权积分。`GaussianQ.lean` 直接定义标准高斯尾函数
  `Q(x)=∫_{x}^{∞} exp(-t²/2)/sqrt(2π) dt`，并证明 `Q(0)=1/2`。借 mathlib 的幂函数换元
  定理，已证明 `Q(sqrt(x))` 等于核
  `k(u)=exp(-u/2)/(2*sqrt(2πu))` 在 `(x,∞)` 上的尾积分；该核在正半轴可积，且
  `Q(0)-Q(sqrt(x))=∫₀ˣ k(u)du`。再将此式代入 layer-cake，得到平均 Q 减量等于严格尾概率
  `P(t<f)` 对 `k(t)` 的积分。对论文 SNR 取 `f=2βλ` 即得到积分变量已缩放的 SER 核表示。
  已进一步证明在概率测度下平均 Q 减量等于 `∫(1-CDF(t))*k(t)dt`；这里严格尾概率与
  `1-CDF` 是精确互补，不需无原子假设。outage 侧弱/严格事件替换的零原子引理也已形式化，
  但 Wishart 最小特征值的零原子性仍未证明。`MIMOWishartSER.lean` 已将此公式特化到
  非中心复 Gaussian Gram 样本的最小特征模增益，并证明均值 Q 减量等于该样本统计量
  SNR-CDF 补函数的加权积分。它仍不是论文 Theorem 1 的行列式 CDF，也还未将减量公式
  改写成完整 SER 本身的期望等式。
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
  对最小 `1×1` 样本进一步证明，该候选式等于 mathlib 单位率指数分布的 CDF；同时已将
  `1×1` 中心 Gram 的唯一特征值化为两个实高斯坐标平方和的一半。`GaussianRadialCDF.lean`
  已闭合分布等式，证明真实最小特征值 CDF 与 Theorem 1 公式候选相等。一般 `t` 下
  坐标能量和的 Gamma 分布仍未证明。
- `GaussianRadialCDF.lean` 也已闭合 Theorem 2 的中心 `1×1` 特例：公式候选在 `x≥0`
  等于指数 CDF，并进一步等于 Wishart 测度下实际最大特征值弱事件 `P(λmax≤x)`。
  这一步直接处理弱事件，没有假设尚未证明的无原子性；更高维 Theorem 2 仍未完成。
- `RadialIntegration.lean` 将 mathlib 的 `MeasureTheory.integral_fun_norm_addHaar`
  特化到复平面，机检得到
  `∫_{ℂ} f(‖z‖) dz = 2π ∫₀∞ r f(r) dr`。这把“二维径向积分”
  环节正式封装了；并新增任意偶数维实内积空间的全空间与闭球版本，径向系数由单位球体积的
  阶乘闭式给出，闭球积分准确落在半开区间 `(0,R]` 上。
  该推广是构造一般中心标量 Wishart Gamma 律所需的几何引理；目前已与二维 Gaussian 密度桥、
  圆盘积分共同推出中心 `1×1` Wishart 的指数分布；一般偶数维的 Gamma CDF 识别仍待完成。
- `GaussianRadialLaw.lean` 已补上上述高斯密度桥：利用 `gaussianReal` 的 PDF、有限乘积
  密度定理、复平面坐标的保体积等价和 mathlib 的 `stdGaussian` 正交基表示，机检证明
  `stdGaussian ℂ` 等于密度
  `(2π)⁻¹ exp(-‖z‖²/2)` 对复平面 Lebesgue 测度的加权测度。这是一个真正的样本测度
  等式，不再只是抽象独立性或协方差结论；该密度的圆盘积分和半径平方 CDF 已在
  `GaussianRadialCDF.lean` 中完成。另已证明任意有限个实标准高斯 PDF 的乘积逐点化为
  只依赖欧氏范数的径向表达式，并证明该有限乘积测度经 `toLp` 后给出 EuclideanSpace
  上的 `stdGaussian` Lebesgue 密度。对任意有限坐标，密度现已写成显式的径向形式。
- 上一项的样本连接现已完成：`centralScalarToComplex` 是 `ComplexSample (1×1)` 到 `ℂ`
  的线性等距等价；标准高斯在该等价下映到 `stdGaussian ℂ`，且样本能量逐点等于
  `‖z‖²/2`。因此 `centralScalarSampleEnergy_map_eq_radialGaussianEnergy` 已将真实的
  `1×1` Gram 能量分布精确归约到上面的复平面径向高斯测度。`GaussianRadialCDF.lean`
  现已完成圆盘内密度积分，证明样本能量、最小特征值的分布均为单位率指数分布，并与
  Theorem 1 中心标量单样本公式侧候选 CDF 接通。这只闭合了 `1×1` 特例，绝不是论文
  多维 Theorem 1 的一般证明。
- `GaussianRadialCDF.lean` 现还将偶数维 EuclideanSpace 的能量阈值事件精确化为闭球，
  并证明球概率等于一维径向积分；通过 `u=r²/2` 的 Lean 换元定理，将径向核化为
  lower-Gamma 型积分。尚差归一化常数与 `gammaMeasure` CDF 的完整对接，以及将一般标量
  Gram 能量识别为该 EuclideanSpace 能量。

这是一项实质性的概率模型和有序谱基础形式化，但还没有得到 Wishart 的 Lebesgue
密度或联合特征值密度；Theorem 1 的公式侧已编码，但还没有 CDF 等式证明，Theorem 2–4
亦未完成。当前 covariance 设为单位阵，尚未覆盖论文中的一般尺度矩阵 `Σ`。最小有序
特征值已作为非中心 Gaussian 样本的可测随机变量，但最大特征值和整组有序特征值的随机
向量层、其联合分布，以及与论文闭式公式的等式仍待形式化。

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
- mathlib 的 `integral_gaussian_Ioi` 可支撑标准 Gaussian-Q 的半轴归一化；本项目已用它
  证明 `Q(0)=1/2`。幂函数积分换元及半轴积分差分还支持上述具体 SER 核表示，但这仍不等于
  完整 MIMO SER 定理，因为随机有序特征值的可测性、CDF 等式和无原子性尚缺。
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
