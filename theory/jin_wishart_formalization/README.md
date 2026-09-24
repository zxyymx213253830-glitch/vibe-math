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

这是一项实质性的概率模型形式化，但还没有得到 Wishart 的 Lebesgue 密度、联合
特征值密度或论文中的 CDF 行列式公式；当前 covariance 设为单位阵，尚未覆盖论文
中的一般尺度矩阵 `Σ`。

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
  本文所需的 Nuttall `Q`、复多元 Gamma 或矩阵变量超几何函数接口。

本次网络和已锁定 mathlib 源码检索没有找到可直接依赖的 Lean Wishart、Nuttall `Q`
或复矩阵变量分布库。因此本项目采用“复用 Gaussian + 矩阵基础库，再在本仓库
补建 Wishart 层”的路线，而非引入一个并不存在的现成 Wishart 包。

## 尚未形式化的论文核心

- 复矩阵 Gaussian 密度，以及一般协方差尺度下非中心 Wishart 的密度表示；
- 一般协方差尺度 `Σ` 下的非中心 Wishart 定义与线性变换定理；
- Hermitian 随机矩阵有序特征值的联合可测性和联合密度；
- 矩阵变量超几何函数、Nuttall Q 函数及复多元 Gamma 函数；
- Theorem 1–3 的行列式 CDF 公式；
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
