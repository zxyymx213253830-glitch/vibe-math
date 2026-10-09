# G2：实际复 Gaussian 矩阵原始坐标密度

本卡属于 2026-10-09 22:09:38–23:09:38（Asia/Shanghai）的一小时工作窗口。
不做 OFDM、单列新特例或其他项目；只解除多列 Wishart 密度链的一项前置。

## 数学结果与边界

`GaussianRawCoordinates.lean` 将任意 `m×n`、任意确定性复均值 `M` 的
实际样本，转换到没有 sqrt(2) 编码倍率的实部/虚部 Euclidean 坐标。
证明其概率律等于体积测度乘密度

`pi^(-mn) exp(-sum_ij |X_ij-M_ij|^2)`。

这里 `X_ij = z_ij,0 + I*z_ij,1`，每个实坐标的方差是 1/2。
`complexSampleMatrix_sqrtTwo_smul`、`rawComplexSampleMean_apply` 和
`rawComplexSample_norm_sq_eq_frobenius` 分别核对无编码倍率的矩阵条目、均值及能量。
`paperJointSpectrum_event_eq_rawDensityIntegral` 把实际小侧全部有序谱事件的
概率写成这个 **矩阵样本空间** 上的积分；没有 `hDensity` 前提。
这不是 Gram 矩阵密度，也不是特征值联合密度；没有解除非单射、降维换元。

## 检索先行及补库复用

按董彬 AI4M 指南的检索→形式化反馈方式，先用
`verification/leansearch_lookup.ps1` 检索有限维 scalar scaling 的体积推前。
服务返回 `MeasureTheory.Measure.map_addHaar_smul`，在锁定 mathlib
`e18afff334217588afc719a8b707b00d90521064` 的
`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean` 核对精确类型。
该代码属 mathlib 现有 Apache-2.0 许可代码；通过 import 直接复用，不复制外部片段。

泛化新增引理 `map_withDensity_smul_euclidean` 对任意可测非负密度、任意非零实缩放
成立，保留绝对值和完整逆 Jacobian，允许负缩放、零维空间；
`stdGaussian_scaled_shift_eq_withDensity` 可复用于其他 Gaussian 矩阵/尺度模型。
这是 **本地补库/现有定理的组合应用**，不是全球首创，也没有上游提交或接收。
公开检索只发送通用数学问题，不发送私有完整源文件、凭证或模型服务请求。

## 数值先行控制（不是证明）

`experiments/gaussian_raw_coordinates_control.py`，固定种子 `2026100914`，
`2×2,3×2,2×3` 各 200000 次，总计 600000 次样本。
独立对照：SciPy 的一维 `N(0,1/2)` PDF 乘积，以及精确 Frobenius 能量均值
`mn + ||M||_F^2`。
结果：最大 log-density 差为 `1.42e-14`；能量均值偏差分别为
`1.474,1.598,0.606` 标准误，全部控制通过，退出码 0。
零维密度质量约定额外核对为 1。

## 验收与最小剩余缺口

验收命令在 `theory/jin_wishart_formalization` 使用项目自己的 ELAN_HOME、
`LEAN_NUM_THREADS=1`：局部模块、`checks/GaussianRawCoordinates.lean`、
主入口构建及公理打印均通过：局部模块构建退出码 0；
`lake env lean -j1 checks/GaussianRawCoordinates.lean` 退出码 0；
`lake build JinWishartFormalization --quiet` 退出码 0。
11 个关键声明的公理打印都只有 `propext, Classical.choice, Quot.sound`。
检查包含任意维数总质量 1、非中心 `3×2` 跨阈值事件和零维密度；
占位/新公理扫描无命中，`git diff --check` 通过（仅既有行尾转换提示）。

下一实质缺口：从这个矩阵坐标密度到 Hermitian Gram 的非单射降维推前，
必须引入 QR/Cholesky 与角变量或其他等价测度论路线，再建立谱 Jacobian、
角积分和非中心核；不得把期望的谱密度作为假设后宣称完成。
`[需人工审查]`：体积约定、单位方差复 Gaussian 与论文模型对应、缩放方向、
谱事件解释。不同模型家族的 P4 审查尚未满足，不能标“审查通过”。
