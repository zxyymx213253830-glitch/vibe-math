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
  所需的无原子性在多列维数仍待证明；任意正行数、单列的非中心情形
  已由下述球面零测定理完成。
  严格 CDF `P(λ_min<x)` 已精确证明为 `1-` 对应 Wishart 移位 PSD 尾事件的概率；
  标量情形已把严格 `<` 与论文使用的弱 `≤` 接通。
- 最大特征值一侧也已完成对应的确定性桥梁：`xI-W` 半正定等价于每个特征值不超过
  `x`，在非零维度下等价于降序列表首项（最大特征值）不超过 `x`；该事件可测，并已
  定义其非中心 Wishart 概率作为 CDF 基础。一般维数尚未证明这一概率等于论文
  Theorem 2 的行列式；`1×1` 特例见下述新模块。
- `MIMOPerformance.lean` 已形式化一般实值统计量在正 SNR 缩放下的 outage 阈值换算：
  弱事件 `cφ≤γ` 精确等于在阈值 `γ/c` 处的 CDF；严格事件 `cφ<γ` 单独保留，不能在
  未证无原子性时替换为弱 CDF；另已证明若相应等值集质量为零，则严格与弱 outage 概率相等。
  多列 Wishart 最小特征值的无原子性尚未证明；单列已证明。还封装了 mathlib 的 layer-cake 定理，将非负随机变量上
  `∫₀ᶠ g` 型误差核期望改写为尾概率加权积分。`GaussianQ.lean` 直接定义标准高斯尾函数
  `Q(x)=∫_{x}^{∞} exp(-t²/2)/sqrt(2π) dt`，并证明 `Q(0)=1/2`。借 mathlib 的幂函数换元
  定理，已证明 `Q(sqrt(x))` 等于核
  `k(u)=exp(-u/2)/(2*sqrt(2πu))` 在 `(x,∞)` 上的尾积分；该核在正半轴可积，且
  `Q(0)-Q(sqrt(x))=∫₀ˣ k(u)du`。再将此式代入 layer-cake，得到平均 Q 减量等于严格尾概率
  `P(t<f)` 对 `k(t)` 的积分。对论文 SNR 取 `f=2βλ` 即得到积分变量已缩放的 SER 核表示。
  已进一步证明在概率测度下平均 Q 减量等于 `∫(1-CDF(t))*k(t)dt`；这里严格尾概率与
  `1-CDF` 是精确互补，不需无原子假设。outage 侧弱/严格事件替换的零原子引理也已形式化，
  但多列 Wishart 最小特征值的零原子性仍未证明。`MIMOWishartSER.lean` 已将此公式特化到
  非中心复 Gaussian Gram 样本的最小特征模增益，并证明均值 Q 减量等于该样本统计量
  SNR-CDF 补函数的加权积分。它仍不是论文 Theorem 1 的行列式 CDF，也还未将减量公式
  改写成完整 SER 本身的期望等式。
- `Theorem1Formula.lean` 已将论文式 (15)–(18) 的 `Ψ(x)` 分段条目和行列式比值编码为
  Lean 定义。它只是精确的公式侧候选值；尚未证明分母非零，也尚未证明它等于上述
  Wishart 尾概率的补数。Theorem 2 的 `Ξ(x)` 条目及式 (19) 的行列式候选值也已编码；
  对应的概率等式同样未证明。
- 已证明 Theorem 1–2 公式之间的逐元素关系 `Ξ(x) + Ψ(x) = Ψ(0)`；对非中心列，
  还在核尾可积这一显式前提下，将 `Q(0)-Q(√(2x))` 改写成有限区间积分。该可积性
  对一般阶数 `(p,q)` 仍未从论文参数推出；`(1,0)` 已证明。另需注意：论文的竖线记号表示行列式，而 Lean 候选式目前
  对复行列式取模长；还需证明相关行列式为实且非负，才能确认两种写法一致。
  另有 `OrderedPositiveNoncentralSpectrum` 及 `...OfSpectrum` 入口，把
  `λ₁ > ··· > λ_L > 0` 编码为结构字段；较底层的 raw 函数仍接受任意实数列，不能单独
  视作论文陈述。即便经 validated 入口，分母非零与候选式等于概率仍未证明。
- 已处理 Theorem 1 的中心标量特例 `s=1, L=0`：形式化了归一化行列式为
  `(t-1)!`、其非零性，以及 `x≥0` 时候选 CDF 化为归一化的整数 Gamma 有限和。
  对最小 `1×1` 样本进一步证明，该候选式等于 mathlib 单位率指数分布的 CDF；同时已将
  `1×1` 中心 Gram 的唯一特征值化为两个实高斯坐标平方和的一半。`GaussianRadialCDF.lean`
  和 `WishartGamma.lean` 已将结果推广到任意正整数 `t`：中心一列样本的真实最小特征值
  CDF 与 Theorem 1 的 `s=1, L=0` 有限和公式相等。非中心 `1×1` 情形见下述新模块；
  非中心多行及 `s>1` 仍未证明。
- `WishartGamma.lean` 还闭合了 Theorem 2 的中心单列特例，对任意正整数行数，公式候选
  等于 Gamma CDF，并等于真实唯一特征值的弱 CDF 事件（此时最大、最小特征值相同）。
  这一步直接处理弱事件；非中心 `1×1` 情形见下述新模块，多列及非中心多行仍未完成。
- `RadialIntegration.lean` 将 mathlib 的 `MeasureTheory.integral_fun_norm_addHaar`
  特化到复平面，机检得到
  `∫_{ℂ} f(‖z‖) dz = 2π ∫₀∞ r f(r) dr`。这把“二维径向积分”
  环节正式封装了；并新增任意偶数维实内积空间的全空间与闭球版本，径向系数由单位球体积的
  阶乘闭式给出，闭球积分准确落在半开区间 `(0,R]` 上。
  该推广是构造一般中心标量 Wishart Gamma 律所需的几何引理；目前已与有限维 Gaussian 密度桥、
  偶数维球积分共同推出一列中心 Wishart 的 Gamma 分布。
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
  lower-Gamma 型积分。偶数维径向 Jacobian 与 Gaussian 密度的常数已单独化简为
  `1/(k-1)!`；该 lower-Gamma 积分也已与 mathlib 的 `gammaMeasure` CDF 完整对接，并证明
  一般偶数维标准高斯能量服从整数形状、单位率 Gamma 分布。
- 新增 `WishartGamma.lean`：将 `m×1` 复中心高斯样本坐标逐点识别为 `2m` 维实欧氏高斯
  能量，证明其唯一 Gram 特征值服从 `gammaMeasure m 1`。这给出了一般行数的一列中心
  Wishart 标量律；并将此 Gamma CDF 与 Theorem 1 中心标量有限和公式在任意正整数 `m`
  下完成等式拼接，得到真实样本最小特征值的 CDF 定理。
- 非中心 `1×1` 情形已补上概率事件的几何降维：最小特征值不超过 `x` 的概率，精确等于
  实高斯向量落入以负均值为中心、半径 `√(2x)` 的闭球概率。后续模块已把该偏心圆盘
  概率化为 Nuttall-Q 尾积分，并完成非中心 `1×1` Theorem 1 的概率等式。
- 新增 `BesselI0Series.lean` 和 `BesselI0Angle.lean`：从 Mathlib 的正则化超几何级数定义
  推出 `I₀` 的精确阶乘级数，并以一致范数可和控制、奇偶拆项和余弦矩递推证明完整角积分
  `∫₀²π exp(a cos θ)dθ = 2π I₀(a)`。`NoncentralScalarCDF.lean` 现在将标量 Nuttall-Q
  核改写为该高斯角平均；`NuttallQZero.lean` 另证明零非中心参数时的 Nuttall-Q 尾为
  `exp(-b²/2)`（`b≥0`）。这些均已独立通过 Lean 构建，但偏心球到极坐标积分的平移、周期
  区间与尾积分拼接由后续模块完成；此模块单独不构成非中心标量 CDF 定理。
- `ScalarNoncentralPolar.lean` 已将复平面上以原点为心的闭圆盘积分精确换成 Mathlib 的
  极坐标图积分，并将圆盘条件化为半径截断；另已证明实轴中心的极坐标距离平方展开，以及
  `[-π,π]` 与 `[0,2π]` 两种角积分区间等价。这验证了极坐标/Jacobian 与标量角周期两步；
  并已证明实轴中心的极坐标高斯核角积分恰为相应的 `2π exp(-(r²+c²)/2) I₀(rc)`。
  一般复偏心中心的旋转和高斯测度换元现由下述新模块处理；圆盘积分与 Nuttall-Q 尾部
  尚未完全拼接。
- `ScalarNoncentralDiskFubini.lean` 已把实中心闭圆盘积分整理成半径优先的乘积积分，并完成
  有界矩形上的 Fubini 论证；再将角积分换成 `I₀` 的实阶乘级数，得到精确的一维径向积分
  `2π·r·exp(-(r²+c²)/2)·I₀(rc)` 在 `(0,R]` 上的积分。这仍是未归一化的实轴中心核，不等于
  任意复均值下的非中心 CDF；总质量归一、Q 尾部和概率事件的最终等式见后续模块。
- `ScalarComplexCenterAngle.lean` 已把上述角积分恒等式推广到任意复数中心：角积分仅依赖
  中心的模长。`ScalarGaussianComplexBridge.lean` 已证明真实标量非中心 Wishart CDF 等于
  复平面中心圆盘上的平移高斯密度积分，包含二维实高斯到复平面的等距映射、密度和积分平移。
  两个模块均已独立通过 Lean 构建。[需人工审查] 测度换元与密度积分的数学建模对应。
- `NuttallQRiceSplit.lean` 已在尾核可积的显式前提下证明
  `Q₁,₀(a,0)-Q₁,₀(a,b)` 等于从 `0` 到 `b` 的 Rice 径向积分。所需 `(1,0)` 尾核
  可积与 `Q₁,₀(a,0)=1` 已在后续模块证明。`Theorem1FullRankDeterminantScaling.lean`
  已证明满秩情形下行缩放因子在 Theorem 1 的行列式比中抵消；它是公式侧代数化简，
  不构成概率分布定理。
- `ScalarComplexCenterDisk.lean` 已把任意复中心的圆盘高斯积分，经极坐标换元、Fubini
  和角积分化成一维 Rice 径向积分。`ScalarNoncentralCDFRice.lean` 随后证明真实标量
  非中心 Wishart CDF 等于该径向积分；在尾核可积的显式假设下，又等于
  `Q₁,₀(a,0)-Q₁,₀(a,√(2x))`，其中 `a` 是真实高斯均值的范数。两模块均已通过
  Lean 构建。[需人工审查] 测度换元及 Gaussian 标度与论文约定的对应。同文件另证明
  任意非负下限的 `Q₁,₀` 尾积分是非负实数。
- `NuttallQRiceMass.lean` 用角积分上界及高斯可积主函数证明实 Rice 核和复 Nuttall-Q
  核在正半轴无条件可积；`NuttallQRiceNormalization.lean` 用标量 CDF 在无穷远处趋于 1
  证明 Rice 核总积分为 1。`ScalarNoncentralTheorem1.lean` 据此证明
  `Q₁,₀(a,0)=1`（`a≥0`），并最终给出无附加可积性/归一化假设的非中心 `1×1`
  Theorem 1 CDF 等式（`x≥0`）。以上均经 Lean 构建；这仍只是论文的标量特例，
  非中心多列的一般定理尚未完成。[需人工审查] 无穷远极限与论文模型约定的匹配。
- `Theorem2NoncentralScalarFormula.lean` 将 Theorem 2 公式 (19)–(20) 在 `s=t=L=1`
  时化成归一化 Nuttall-Q 增量，随后调用已证明的可积性与总质量结果，得出其候选式
  等于同一真实非中心标量 CDF（`x≥0`）。一般矩阵维数的 Theorem 2 仍未完成。
- `OrderedEigenvalueCDFRecurrence.lean` 已证明 Theorem 3 公式 (22) 的事件分解原理：
  对有序可测统计量 `a≤b`，`P(a≤x)=P(b≤x)+P(a≤x<b)`（Lean 中增量事件写为
  `a≤x ∧ x<b`）；它不需要无原子假设。论文后续的行列式求和式 (23)–(25)
  尚未形式化，且论文使用的严格排序事件还需相应的零重根/边界质量论证。
- `OrderedEigenvalueStrictRecurrence.lean` 证明若下方统计量在阈值 `x` 无原子，
  则递推增量可改写为严格事件 `a<x<b`。将其用于一般多特征值模型还需证明
  对应有序特征值无原子及零重根。
- `OrderedEigenvalueIndexedRecurrence.lean` 将此原理写成有限个降序可测统计量
  的相邻 CDF 递推，并证明“阈值严格位于相邻两项之间”等价于论文所用的
  整条序列阈值分割事件；它仍是抽象概率定理，尚未代入多特征值 Wishart 随机矩阵。
- `OneColumnNoAtom.lean` 将无原子性推广到任意正行数的单列复非中心 Wishart；
  `BesselI1Series.lean` 给出四维径向计算将用到的修正贝塞尔函数 `I₁` 级数。
  二者尚未构成两行单列非中心分布的完整解析证明。
- `OneColumnCDFRecurrence.lean` 把无原子性用于真实单列 Wishart 特征值律，
  证明 CDF 的弱阈值事件与严格阈值事件概率相同。单列只有一个特征值，
  因而这里的有序对递推是退化情形，并未证明多特征值的 Theorem 3。
- `Theorem1SingleColumnTwoRows.lean` 将 Theorem 1 的 `s=1,t=2,L=1` 公式侧
  化为 `Q_{2,1}` 尾比；`NuttallQ21Positive.lean` 已证明幅度 `a>0` 时
  实核可积且严格为正，因此 `Q_{2,1}(a,0)≠0`。尚未证明该候选式等于真实分布。
- `Theorem1SingleColumnAnyRows.lean` 将上述公式侧约化推广到任意 `t≥1`：
  尾函数是 `Q_{t,t−1}`。这一推广仍以分母非零为明确前提，也尚未连接真实分布。
- `Theorem2SingleColumnAnyRows.lean` 将 Theorem 2 的同一单列公式侧化为
  归一化的 `Q_{t,t−1}(a,0)-Q_{t,t−1}(a,√(2x))` 增量；同样仍需分母非零
  和实际多行非中心分布的解析连接。
- `Theorem1TwoRowsNoncentral.lean` 用 `Q_{2,1}` 的已证正性，在 `λ>0`
  时消除 `t=2` 两条公式侧结论的显式分母非零前提；实际 CDF 等式仍未证明。
- `NuttallQ21Normalization.lean` 现已从 Bessel `I₁` 的非负级数逐项积分，
  证明实核总积分为幅度 `a`，并桥接到复值定义
  `nuttallQ 2 1 a 0 = (a : ℂ)`（`a>0`）。该结果消除了 `Q₂,₁` 的标量
  归一化缺口，但并不单独证明真实 `2×1` 样本的径向分布。
- `Theorem1TwoRowsNoncentral.lean` 现将双行单列的 Theorem 1/2 公式侧归一化项
  精确化简为实幅度 `√(2λ)`；这仍是特殊函数公式化简，不代表概率等式。
- `NoncentralOneColumnEnergy.lean` 对任意正行数证明真实单列非中心 Gram 最小
  特征值等于平移后实高斯向量的平方范数除以 2，并将 CDF 子水平事件精确写成
  以负均值为中心、半径 `√(2x)` 的闭球概率。该模块给出了 `2×1` 模型到四维高斯
  球概率的入口；并将该 CDF 表示为有限维标准高斯的平移密度积分。
- `GaussianEuclideanBallDensity.lean` 从 Mathlib 有限维标准 Gaussian 密度定理
  推出闭球概率的 Lebesgue 积分形式，并证明平移闭球的积分换到以原点为中心的球，
  指数核相应变成 `exp(-‖z-μ‖²/2)`。该模块尚未计算四维球面的角积分。
- `SphereThreeMeasure.lean` 由 Mathlib `toSphere` 定义和三维单位球体积证明
  三维单位球面的总质量为 `4π`；它是 S³ 角积分分解的基础常数校验，还未证明 S³
  的单极角 chart 公式。
- `SphereFourDAngularIntegral.lean` 已建立 R⁴ 与 `ℝ × R³` 的测度保持坐标分解，
  并利用四维极坐标定理证明角因子与半径因子的乘积分解；另已证明一般三维径向积分
  恰为 `4π` 乘相应的一维径向积分。一个单位球 cutoff 的径向积分已精确算为 `1/4`。
  R×R³ 方向的 Fubini/复极坐标计算尚未完成，
  因而仍未得到 S³ 到单极角 chart 的恒等式。
- `SphereFourDPlanePolar.lean` 已证明 R⁴ 到 `ℝ × R³` 坐标下的首坐标、范数平方分解，
  并将球面角测试函数逐点化为仅依赖标量坐标与三维半径的 slice 函数。已证明该 slice
  可积（使用紧支撑与指数上界），并用 Fubini 和 R³ 径向公式将 Cartesian R⁴ 积分
  精确化为 `ℝ` 上标量坐标与 `volumeIoiPow 2` 上半径的迭代积分，内层角因子为 `4π`。
  尚未完成将该半平面积分通过复平面极坐标识别为 S³ 单角 chart 的角积分。
- `SphereFourDPlaneAngleChart.lean` 继续补上了点态 chart 引理：在 `r>0`、`0<θ<π` 时，
  slice 等于 `if r<1 then exp(κ cos θ) else 0`；乘以平面极坐标 Jacobian 后，integrand
  精确成为 `if r<1 then r³ sin²θ exp(κ cos θ) else 0`。还证明 `volumeIoiPow 2` 的积分
  可展开为 `r² dr`，并把主线标量-径向积分改写成正半平面上的带 `ρ²` 权重积分。
  已证明 Mathlib 主值极坐标 chart 内虚部为正恰等价于 `θ∈(0,π)`。这些局部结果均已
  导入主入口并通过完整构建；但加权半平面积分到复极坐标 chart 的测度换元尚未闭合，
  所以仍不能推出 S³ 单角 chart 等式或真实 `2×1` CDF。
  此外，现已证明 `ℝ × Ioi(0)` 上的 `volume × comap(Subtype.val, volume)` 经坐标映射后，
  正好是 `ℝ²` 上限制到上半平面的 Lebesgue 乘积测度；这为把该迭代积分改写为复平面
  集合积分准备了测度层桥梁，但带权积分等式本身尚未完成。
- `NoncentralFourDimensionalRadial.lean` 严格核对四维径向*核*等于
  `Q_{2,1}` 的被积函数除以非中心幅度。
- `BesselI1Angle.lean` 与 `NoncentralFourDimensionalSphere.lean` 已机检
  `S³` 单极角 chart 的解析积分，以及它与四维高斯密度、`r³` Jacobian
  相乘后的 `Q_{2,1}` 核系数；`NoncentralFourDimensionalTail.lean` 在显式
  可积性前提下证明该径向核的尾积分等于 `Q_{2,1}(a,b)/a`。尚未证明此
  chart 公式代表真实球面测度 `[需人工审查]`，因此实际 `2×1` CDF 尚未闭合。
- `FourDimensionalPolarBridge.lean` 已进一步用 Mathlib 的 `toSphere` 测度
  证明真实四维移位高斯球积分的“单位球面 × 半径”极坐标换元。
  目前唯一缺口是把该真实球面测度的角积分识别为上面的单角 chart 积分
  `[需人工审查]`；因此尚不能推出实际 `2×1` CDF 等于 Nuttall-Q 公式。
- `NoncentralFourDimensionalPoissonMixture.lean` 证明四维候选径向核逐点等于
  Poisson 加权的中心 Gamma 径向核级数。这提供另一条解析路线；真实移位 Gaussian
  测度等于该混合的证明仍未完成。
- `OrderedEigenvalueMeasurable.lean` 补充最大与最小谱值的可测性引理；一般内部
  有序特征值向量的联合可测性仍未证明。`ScalarPhysicalScaling.lean` 证明正散射尺度
  下标量能量的确定性归一化恒等式，不代表一般矩阵协方差的参数变换已完成。
- `ScalarNoncentralSmallX.lean` 将真实非中心 `1×1` CDF 写为半径加权积分，
  且证明连续因子在零处是 `exp(-λ)`。`WeightedIntervalAverage.lean`
  完成连续函数的加权区间平均极限；`ScalarNoncentralSmallXLimit.lean`
  据此证明真实 `1×1` 非中心 CDF 的 `F(x)/x → exp(-λ)`，即 Theorem 4
  在此特例的小阈值首项。这里 Lean 的 `M` 是单位复方差模型的均值；
  对论文原始信道需先除以散射尺度 `ε`，才能与其 `Ω` 参数匹配
  `[需人工审查]`。一般特征值渐近及后续 SER 渐近仍待证明。
- `ScalarNoncentralOutageAsymptotic.lean` 把上述真实 `1×1` CDF 首项
  转成固定正阈值 `γ` 下的大尺度极限
  `c·F(γ/c) → γ exp(-‖M₀₀‖²)`，并将同一结论直接写成真实弱 outage
  事件 `P(c·φ≤γ)` 的极限。论文标量系统需再代入
  `M_Lean=M_paper/ε`、`c=ε²P`；这项参数映射以及论文低阈值
  叙述与此处固定阈值高 `P` 极限的量词对应尚未在 Lean 中编码
  `[需人工审查]`。一般 MIMO 的 SNR/尺度参数变换仍未完成。
- `ScalarNoncentralNoAtom.lean` 已证明非中心 `1×1` Gram 特征值在每个实数点的概率
  均为零：其等值集在二维高斯样本空间是一个球面，而高斯测度对 Lebesgue 测度绝对连续。
  因此同模块已证明严格次水平集概率等于闭区间 CDF，可用于后续 SER/中断概率的
  事件边界处理。[需人工审查] 球面零测与论文随机模型之间的参数对应。

这是一项实质性的概率模型和有序谱基础形式化，但还没有得到 Wishart 的 Lebesgue
密度或联合特征值密度；Theorem 1–2 的公式侧已编码，中心单列与非中心 `1×1` 特例已有
CDF 等式证明；非中心多行/多列的一般 Theorem 1–2 与 Theorem 3–4 仍未完成。当前 covariance
设为单位阵，尚未覆盖论文中的一般尺度矩阵 `Σ`。最小有序
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
  `q=0,p=1` 的 Rice 情形已补齐可积性与归一化；其余论文所需阶数的相应
  分析性质仍待证明。

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
