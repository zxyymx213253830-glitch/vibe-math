# 实际多列 Gram 非对角项：固定第一列的完整 Gaussian 律

续开窗口 22:42:03–23:42:03，本卡在 23:00 前进入验收。
不是单列 CDF 的追加特例，直接解除多列 Gram/Bartlett 分解的一项依赖。

## 精确结果

`GaussianComplexInnerProductLaw.lean`：

1. `complexColumn_real_inner`：核对实际 `EuclideanSpace ℂ (Fin m)` 的 ℝ 内积
   与复内积实部相同。其 ℝ 实例不与限制标量引理直接匹配，改用现成极化恒等式；
   明确指定复标量，避免重写时错误推断标量。
2. `real_inner_complex_inner`：复内积线性泛函的实特征函数频率对应。
3. `charFun_stdGaussian_complex_inner` 与 `stdGaussian_complex_inner_law`：
   对任意复列 a，实际标准 Gaussian 推前 `z ↦ ⟨a,z⟩` 的 law 等于
   `g ↦ ||a|| g` 的标量标准复 Gaussian law，包括 a=0。
4. `actualComplexColumn_inner_law`：明确实际圆对称单位复方差的 `/sqrt(2)`；
   第二列编码样本 v 的 `⟨a,actualComplexColumn v⟩` 等于
   `g ↦ ||a||/sqrt(2) g` 的推前。
5. `twoColumnGram_offDiagonal_fixed_first_law`：任意 m、任意固定首列编码 u，
   实际 m×2 样本的 Gram (0,1) 条目具有上述完整标量 Gaussian law。

这里的 `stdGaussian ℂ` 本身实/虚部各方差 1，实际单位复方差列需除 sqrt(2)。
固定实际 a 后非对角项 E|b|²=||a||²；这说明常数与论文样本约定相符。
Lean theorem 是测度相等，不把目标密度放入假设。

## 检索复用

实际 LeanSearch 与 LeanExplore 查询见 `AI4M_RETRIEVAL_FIRST_RENEWAL_20261009.md`。
采用锁定 mathlib 的 `charFun_stdGaussian`、`charFun_map_smul`、
`Measure.ext_of_charFun`、`stdGaussian_map` 与 `Measure.map_map`。
没有从头证明 Fourier 唯一性、Gaussian 特征函数或正交坐标不变性。
首次限制标量重写实例不匹配；第三条路线由精确源码的极化恒等式直接解决，
未继续盲试随机 tactic。新文件是本地组合/模型桥，不是首创或已被上游接收。

## 数值先行与验收

`experiments/complex_inner_gaussian_control.py`：seed=2026100942，
m=2,3,5 各 200000 个独立实际单位复方差样本。
已知能量 ||a||² 与已知特征函数 exp(-||a||² |t|²/4) 对照：
能量偏差 .861、1.670、.703 个标准误；最大特征函数偏差
1.385、1.561、1.261 个标准误。退出码 0。数值只是对照，不是证明。

模块 `lake build JinWishartFormalization.GaussianComplexInnerProductLaw --quiet`
退出码 0。`lake env lean -j1 checks/GaussianComplexInnerProductLaw.lean`
退出码 0：3×2 实际 Gram 条目、零向量与实际内积实例的回归通过。
六条公共引理公理仅 `propext / Classical.choice / Quot.sound`。
`lake build JinWishartFormalization --quiet` 退出码 0；无占位证明/新公理，
`git diff --check` 通过（仅行尾转换提示）。

## 最小剩余数学缺口

固定首列的非对角项 law **不等于** (Gram11,Gram12,Gram22) 的联合密度。
还需与正交残差的独立性、残差能量 Gamma law、对随机首列的可测/迭代积分桥，
继而矩阵/谱变量换元与角积分。非中心情形还需移位残差/特殊函数核。
本卡不宣称 T1–4 一般多列定理完成。

`[需人工审查]` 复内积共轭方向、方差尺度、推前测度与论文模型解释。
不同模型家族 P4 尚未完成，内核通过不等于论文对应已经审查通过。

复用价值：复 Gaussian 线性投影、随机矩阵、通信匹配滤波、复回归与 QR 随机律。
