# G2：实际两列样本的外层/内层积分与随机框架变换

## 数学卡片

改动只涉及 `GaussianTwoColumnIntegration.lean`、对应 checks/数值控制、
facade 和追踪文档。维数为任意 `m×2`，包括零行，均值 `M` 可任意。

1. `stdGaussian_sum_split` 证明分离实坐标块后的真实 Gaussian 是乘积测度。
2. `twoColumnIndexEquiv` 是显式第一列/第二列坐标重排；对应 `twoColumnReindex`
   是实线性等距等价。`twoColumnSplit_law` 没有独立性假设，而是证明实际样本的乘积律。
3. `twoColumnJoin_complex_first/second` 核对两列条目就是
   `(u_real+I*u_imag)/sqrt(2)`、`(v_real+I*v_imag)/sqrt(2)`。
4. `twoColumn_lintegral_eq_iterated` 直接证明真实矩阵样本积分可以先固定第一列，
   再积分第二列，非负可测测试函数不需要暗含绝对可积性。
   `paperTwoColumnSpectrum_event_eq_iterated` 将这个结论实例化到非中心实际整谱事件。
5. `twoColumn_gaussian_fiber_rotation`、`twoColumn_rotated_split_law` 证明：
   **只要** `R(u)` 是实线性等距等价且 `(u,v) -> R(u)v` 联合可测，
   第一列依赖的第二列旋转仍保持实际 Gaussian 乘积律。
   不需要错误地假设 `R(u)` 与第一列独立。

最后一项的假设是旋转操作本身的可测性，不是待证 Wishart 密度。
它没有构造 QR 对齐的旋转族，也没有证明 Bartlett、Gram 或联合谱密度。
一般实正交变换不保证保留复内积；后续真正的复 QR 框架还须使用复酉变换，
不能将所有实等距变换都叫作保 Gram 的复酉变换。

## 已有库复用

锁定 mathlib `e18afff334217588afc719a8b707b00d90521064`：
`map_pi_eq_stdGaussian`、`stdGaussian_map`、
`measurePreserving_sumPiEquivProdPi`、`Measure.map_prod_map`、`lintegral_prod`，
以及 `MeasurePreserving.skew_product`。
后一条经 LeanSearch 通用数学描述查询命中并核对本地精确类型；它正好处理
研究检索报告指出的“固定正交投影不能直接替代随机 QR”问题中的乘积保测度部分。
许可为 mathlib 的 Apache-2.0，直接 import 使用。

本地新增的是实际模型坐标与现有基础定理的连接；不是全球首创，没有上游接收记录。
跨项目价值：两块 Gaussian 数据、随机基底/预处理、逐列随机矩阵推前中的严格
Tonelli 和框架变换桥。没有安装大模型证明服务或改变工具链。

## 数值控制（不是证明）

`experiments/gaussian_two_column_control.py`，种子 `2026100922`。
`m=2,3,5` 各 200000 次，已知对照包括列能量 Gamma(m,1) 的均值 m、
独立列能量的中心乘积期望 0、Gram 非对角元素平方模期望 m、
Gram 行列式期望 `m(m-1)`。12 项偏差最大 1.822 标准误；全部通过，退出码 0。

## 验收/审查边界

局部直接 Lean、局部模块构建、`checks/GaussianTwoColumnIntegration.lean`、
主入口 `lake build JinWishartFormalization --quiet` 均退出码 0。
11 项关键公理打印均只有 `propext, Classical.choice, Quot.sound`。
检查覆盖实际非中心 `3×2` 跨阈值事件、零行乘积律和恒等条件框架。
`[需人工审查]`：坐标块与实际复列对应，非负 Tonelli，以及依赖首列的变换
可测性条件是否适用于后续选定的 QR 构造。不同模型家族的 P4 审查未满足。

最小下一个缺口：构造/处理真正的复酉对齐框架，计算固定首列时 Gram
非对角坐标与残余能量的联合律，再完成到 Hermitian Gram 坐标的降维推前；
随后仍缺谱 Jacobian、角积分和非中心核。一般 Theorem 1–4 仍未完成。
