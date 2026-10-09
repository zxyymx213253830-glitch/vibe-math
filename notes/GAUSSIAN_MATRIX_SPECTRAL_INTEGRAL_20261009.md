# 任意维矩阵 Gaussian 到谱事件样本积分（2026-10-09）

## 本卡实际目标

补齐多列谱密度推导的输入：实际移位 Gaussian 样本的密度及其谱事件积分。
只使用当前单位复方差、实标准 Gaussian 编码，不扩展一般协方差。
不再添加一个以待证 `hDensity` 为前提的谱密度接口。

## 精确范围

`GaussianMatrixSpectralIntegral.lean`：任意 `m,n`、任意复均值矩阵 `M`。
每个复元素由两实标准 Gaussian 坐标除以 `sqrt(2)` 编码，实均值
`mu = complexSampleMean M`；Lebesgue 测度是这 `2mn` 个**实编码坐标**的体积测度。

- `stdGaussian_shift_eq_withDensity`：任意有限维 Euclidean 空间，实际移位 Gaussian
  law 恰为 `volume.withDensity (ofReal rho(z-mu))`，不只处理球的概率。
- `paperJointSpectrum`：论文小侧 `min(m,n)` Gram 的完整降序有序谱。
- `paperJointSpectrum_add_mean`：均值的实编码平移与实际复均值加法逐点对应。
- `paperJointSpectrumLaw_eq_density_pushforward`：实际非中心谱 law 是中心谱映射
  对这个已证移位 Gaussian 密度的推前。
- `paperJointSpectrum_event_eq_densityIntegral`：任何 Borel 谱事件的真实概率，
  等于其中心谱映射逆像上的移位密度样本积分。无候选密度前提。

**积分仍在样本空间，不在谱空间。** 它不声称 `rho` 是谱密度，不解决
Gram 降维、酉群角变量、排序域及谱 Jacobian，也不直接证明 T1–T3 行列式概率公式。
尤其不可把这里的体积测度混同原始复矩阵条目坐标：`sqrt(2)` 缩放影响 Jacobian。

## 复用与补库价值

直接复用既有 `stdGaussian_euclidean_eq_radialDensity`、谱可测性以及 mathlib 的
平移保测度、可测等价和推前组合；不重证多维 Gaussian Fubini 或谱连续性。
原本仅在 `GaussianRadialLaw.lean` 内部使用的
`map_withDensity_measurePreserving` 现公开为可复用接口，原数学证明未修改。
通用移位 law 与概率事件积分可用于矩阵统计/其他有限维 Gaussian 模型；
这是本地接口补充，不声称首次形式化或已贡献 mathlib 上游。

## 数值控制

`experiments/gaussian_matrix_density_control.py`，种子 `20261009`。
对 `2×2`、`3×2`、`2×3` 任意小复均值，每模型 200000 个实际样本：

- 比较逐坐标 SciPy Gaussian log PDF 与密度比
  `exp(-||mu||²/2 + <z,mu>)`，并核对复能量等于实范数平方的一半。
- importance-weight 总质量与已知 1 对照，最大偏差 `1.810` 个标准误。
- 真实移位谱事件与未移位谱事件的加权积分对照，最大偏差 `1.787` 个标准误。
- 运行退出码 0；不是线性信息不等式，infoq Oracle/LP 不适用；数值不是证明。

## 验收记录及下一缺口

模块构建退出码 0。`checks/GaussianMatrixSpectralIntegral.lean` 的具体 `2×2`
T3 跨阈值事件和任意矩形维数总质量均通过（`lake env lean -j1`，退出码 0）。
四个关键 theorem 的公理均仅 `propext / Classical.choice / Quot.sound`。
主工程 `lake build JinWishartFormalization --quiet` 于 13:15 UTC 前退出码 0。
早先并行构建出现私有依赖读取失败及 `std::bad_alloc`；原依赖文件仍存在，
设置 `LEAN_NUM_THREADS=1` 后原样主构建与测试通过，未修改依赖或降级证明。
`git diff --check` 无空白错误，新模块无证明占位或新公理。
[需人工审查] 实/复体积约定、平移符号、整谱事件与论文模型对应。
独立跨模型家族审查未完成；不提升为审查通过。

下一步将这个样本积分变换到合法的 Gram/谱和角变量坐标，再应用已经复用的
Andréief 积分定理。缺的是这个降维/角变量桥，不是 Gaussian 原始样本密度本身。
