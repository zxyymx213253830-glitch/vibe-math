# P4 审查交接包：待 Claude / 人工审查

状态：**准备完成，未进行有效 P4；不等于审查通过。** 本地 DeepSeek-Prover 不再承担审稿。

请按 AGENTS 的 P4，只报告问题，不重写证明。每项给出：严重程度、源文件和声明、具体遗漏/错配、为何内核通过仍不能排除模型解释问题。没有发现问题时只能写“在本次范围未发现具体问题”，不能替代人工核对。

源文件及其项目内传递依赖、SHA256、声明清单见 `WISHART_P4_REVIEW_MANIFEST.json`。审查前重新核对哈希；源码改变则单独标记需重新审查的声明。历史 DS 无关回应不作为审查证据。

## 1. 优先审查 2×1 实际模型链

入口：`Theorem1TwoRowsActualCDF.lean`，包括中心/非中心分支及 Theorem2 同一标量特征值的识别。

- `ComplexSample` 标准实 Gaussian 是否经 `/sqrt 2` 对应单位复方差？均值编码是否满足 `‖encodedMean‖²=2‖M‖²`，所有 λ 匹配假设是否准确带入？
- 旋转/基变换是全概率律保持还是仅球概率？任意非零均值到轴向时，零均值是否单独处理？
- 四实坐标球/柱积分的面积常数、半径平方与 t 阈值是否一致？换元 Jacobian 和球面体积是否在同一 Lebesgue 规范下？
- Tonelli/Fubini 使用的是非负核还是已证绝对可积核？复杂特殊函数转换是否引入未经证明的“实数性/正性/非零”假设？
- Nuttall-Q、上下不完全 Gamma、复行列式模长与原文行列式记号有无差异？结论是否只在 x≥0 与 λ>0 的明确参数域成立？

## 2. 中央复 2×2 实际链

入口：`TwoRowActualDensity` → `TwoRowActualNormalizedDensity` → `TwoRowHermitianThreshold` → `TwoRowSmallestEigenvalueCDF` → `TwoRowMinimumLaw` → `Theorem1CentralTwoRowActualCDF`。

- Bartlett 量来自真实 Gaussian 样本吗？投影/残差的独立是实际条件律/联合律，还是把“不同变量”误当独立？随机首列取零时如何零测排除？
- Γ(2,1)、Exp(1)、CN(0,1) 的率/方差是否一致？复坐标到实坐标是否无遗漏 π 或 2 因子？
- Gram chart 的 Fréchet Jacobian 是 S；推前密度用逆 Jacobian 1/S。域、可逆性、边界、测度限制、真实支撑是否全部对应？
- 正定锥是在四个实 Hermitian 坐标上的体积，不是在全部复矩阵空间的体积。密度 `π^-1 exp(-trace)` 的质量1是否连接实际概率律？
- 正定平移事件是 `min>x`；其补集是 `min≤x`。mathlib 谱降序，最后下标是最小值。负阈值、x=0、无原子和严格/弱事件有无混淆？
- 原 Theorem1(s,t,L)=(2,2,0) 候选的分母和 Gamma 行顺序是否与原文逐式对应？不得把这一特例当一般 T1 或一般联合谱密度。

## 3. 新缩放链

入口：`TwoRowScaledMinimum.lean` 与原样本地 proof body `DeepSeekScale20261015/SampleMatrix.lean`。

- 实际对象是 `twoRowActualMinimum (a • z)`；Gram 比例 a²、复条目方差 v=a²、指数率 2/a²。不得把振幅 a 与方差 v 混名。
- a>0 和 v>0 假设不可遗漏；本次不声称零尺度或任意非标量协方差版本。
- 实际概率律由点态谱缩放与已有实际 Exp2 律组成，未假定目标密度；确认形式化陈述没有把目标结论藏在前提中。

## 4. 3×1 后续

入口：`Theorem1ThreeRowsActualCDF.lean`。重复核对均值方向、六实维球体积、Fubini/半径换元和参数映射；此次仅备好哈希，不声称已审查。

## 5. 新中央通用路线的审查边界

`CentralHermitianCoordinates` 的体积是 n² 个实 Lebesgue 的乘积推前；验证其编码可逆，不把全部复矩阵体积限制在零测 Hermitian 子集。
`CentralWishartConeIntegral` 只是候选核积分等式，既未证明也未假设实际一般密度。等式可允许负 x；转用实际谱尾概率时必须 x≥0，或保留额外实际 PD 支撑指标。平方情形核的总质量未被当作1。
`GaussianOrthogonalProjectionLaw` 只处理固定确定性子空间；投影后半范数平方的 Gamma 形状来自显式实维 2k。检查从固定子空间到随机先前列的条件律是否仍缺证明，不能把这一新 Gaussian 定理误当一般 Bartlett 独立/联合谱密度已完成。

## 6. 参考测度修订的额外义务

`HermitianCoordinateMetric` 八条声明已内核通过：一般维数的坐标 Frobenius 能量、2×2 显式归一化框架及实际密度换参考测度。审核时区分“显式框架推前测度等于两倍坐标测度”与“内在定义的 Frobenius 子空间体积”；后者的几何解释仍需人工确认。一般维数的体积因子在正文作为几何比较，不冒称已建立一般实际 Wishart 律。

2026-10-16 的真实只读 Claude CLI 调用以 HTTP/API 402 余额不足中止，没有有效问题报告；原请求和回应保存在 `verification/publication_checks/independent-review-20261016/`，不能算 P4 完成。新的96文件逐字节 manifest 与22个论文主张相配。可将本交接包交给已具备访问权限的独立审查人，不需要重新调用本地 DeepSeek 审稿。

## 审查记录

审查人/模型家族：**已进行一次跨家族语义审查**——WorkBuddy（Step 模型家族，与 Codex/GPT、DeepSeek 均不同家族），2026-10-16。完整回应见 `WISHART_P4_REVIEW_RESPONSE_20261016.md`（含实际读取文件清单、哈希前置核对、分区结果、问题清单 I-1…I-6、未审查范围）。结论：中央 2×2 主链及 2×1/3×1/缩放/中断率/固定子空间/T4/Frobenius 参考测度范围内未发现具体数学问题；问题均为文档精度级。**该回应不替代人工数学审阅；内核 PASS 不等于语义验证。**

原始记录（历史）：审查人/模型家族：待填写。实际读取文件与哈希：待填写。具体问题：待填写。

所有测度、方差及论文对应仍 `[需人工审查]`。独立数值控制不替代这些审查。
