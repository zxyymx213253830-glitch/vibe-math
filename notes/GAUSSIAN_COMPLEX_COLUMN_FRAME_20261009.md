# G2：真实两列样本的复酉框架接口

此卡在 22:37 左右开始，用户于 22:42:03（Asia/Shanghai）追加一小时工作授权。
前两项已完成提交 `ce08664`、`eb731cb` 不重复记为本轮新成果。

## 复用与正式结果

通过 LeanSearch 定向检索，在锁定 mathlib
`e18afff334217588afc719a8b707b00d90521064` 复用
`Pi.orthonormalBasis`、`Complex.orthonormalBasisOneI` 的实正交基，
避免手写实/复范数等价、逆函数和 Gaussian 旋转不变性的证明。
Sigma/Prod 指标用现成 `Equiv.sigmaEquivProd` 及 `piLpCongrLeft` 对接；
其余继续复用 `stdGaussian_map`、`skew_product` 和两列积分桥。
全部为 mathlib Apache-2.0 现有代码，直接 import，不改依赖配置。

`GaussianComplexColumnFrame.lean`：

- `complexColumnCoordinates`：实 `2m` 坐标到复 `m` 列的实线性等距等价，
  条目明确为 `u_real + I*u_imag`；实际复 Gaussian 列另除 `sqrt(2)`。
- `encodedComplexFrame`：真正的复线性等距等价（复酉框架）转成编码实坐标操作。
- `twoColumn_complex_fiber_frame_law`：对于联合可测的首列依赖复酉框架，
  首列与被该框架变换的第二列仍具有实际 Gaussian 乘积律。
- `complexColumnPair_gram_entry`：两列 Gram 元素就是复内积。
- `twoColumn_actualGram_unitary`：对同一固定复酉框架变换两个实际列，
  完整 `2×2` Gram 矩阵严格不变；不把一般实正交变换错当成保复 Gram 的变换。

不声称对齐首列后首列仍 Gaussian；没有构造具体可测 QR 框架，
没有证明残余能量分布、Bartlett、Gram 密度或联合谱密度。
这里旋转族可测性是假设操作可测，不是假设待证分布。

## 数值先行控制（不是证明）

`experiments/complex_two_column_frame_control.py`，固定种子 `2026100923`，
200000 组实际 `2×2` 复 Gaussian 样本。显式两行酉矩阵把首列对齐正实轴。
与 `UᴴU=I`、对齐结果、复内积不变三个确定性参考式对照，最大误差分别
`8.88e-16,2.22e-15,4.46e-15`；残余平方模的 Exp(1) 均值对照偏差
3.062 标准误，通过控制、退出码 0。这不证明该具体框架的可测性或残余 law。

## 验收及最小缺口

局部直接 Lean 和目标模块构建退出码 0；checks 退出码 0，12 个关键公理
打印只有 `propext, Classical.choice, Quot.sound`。
主入口 `lake build JinWishartFormalization --quiet` 退出码 0。
未编译的论文一般密度不计为完成。
下一步优先用已有 Gaussian 投影/特征函数工具计算固定首列时非对角复内积律，
再证明与正交残余能量的联合律；谱 Jacobian、角积分和非中心核仍缺。
`[需人工审查]` 实/复坐标与方差约定、框架可测性假设、模型解释。
跨家族 P4 尚未通过；本地组合补库，不宣称首创或上游接收。
