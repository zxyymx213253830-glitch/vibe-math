# 固定无噪声撑满条件下的实际行 Gram logdet 偏移

2026-10-20 10:13UTC 新一小时。证明作者 Codex；Qoder 只负责路线分析与不同家族 P4。

固定 B:p×n、M:m×n，Z:m×p 独立 proper CN1，X=ZB+M，m>0。
假设 s=rank(M restricted kerB)=m。上一轮已证固定 C 满足 BC=0、MC=I，
因此所有 Z 的 ROW Gram W=XX^H 最小值至少固定 delta>0。
这是额外的结构条件，并非对任意固定 B/M 都成立；不要求 m<=p。

本轮机检定理：

1. 实际 ell(Z)=log(Re det W) 可测且绝对可积。
2. Delta(rho)=E log(Re det(I_n+rho X^H X))-m log rho-E ell，rho>0。
   对同一个固定 delta，0<=Delta(rho)<=m/(rho delta)。
3. 因而期望 full logdet 减 m log rho 收敛到 E ell，并有上述 O(1/rho) 界。

证明短路线：Sylvester 在同一样本上比较 I_n+rho X^H X 与 I_m+rho XX^H。
正行谱给 e_r=SUM log(1+1/(r lambda_i))，0<=e_r<=m/(r delta)。
先在 r=1，由 C(1) 已有 L1 和有界可测 e_1 得 ell=C(1)-e_1 的真 L1；
再对一般 r 积分并夹逼。不依赖未证的相关模型转置分布，也不先假设偏移可积。
若 n>m，列 Gram 奇异并不影响 I_n+rho X^H X 的正则化 logdet，偏移仍取行 Gram。

源码 NoiselessRowLogDetError(4)、BoundedOffsetExpectation(3)、
CorrelatedNoiselessLogDetOffset(4)；11 项是辅助引理与实际定理总数，并非11个独立研究突破。
最终叶子检查全部 exit0，打印仅 propext/Classical.choice/Quot.sound。
数值前检使用上一轮200000固定种子实际CN1样本，15项已通过；不是一般证明。
新增首阶/二阶候选前检27项，90位精度、精确有理标量输入、独立正积分及已知闭式对照，
此时只是下一目标的控制，首阶逆矩阵迹系数仍待补。

## Qoder P4 原始问题与裁决

三个完整最终源码快照、prompt、raw response 和 receipt 均保留并加入审计。

- deterministic P4 将 complexGram 错写为 XX^H。实际定义为 X^H X，
  因而 complexGram X^H=XX^H 为 m×m。n=0 时也为 m×m 零矩阵；
  正 delta floor 假设不可满足，不存在“0×0最小值”的调用。
- smallestEigenvalue index 本身是 Fin(card(Fin b))；排序已由 pinned
  eigenvalues_0_antitone 定理显式使用。不存在缺失的排序假设或未处理的类型强转。
- Sylvester 定理明确支持矩形乘积；无需随机谱补零的测度运输。
- Hermitian 正谱 logdet 等式由谱乘积证明，已包括 det 实且正；不是浮点噪声。
  Real.log 是总定义可测函数，其可测性无需先证明输入正；数学正谱身份另有证明。
- generic P4 称 squeeze_zero' 参数错误，与固定 mathlib 真正签名相反：
  它恰好接受两个 Eventually 界和一个 Tendsto 上界。最终 exit0 与三公理打印均记录。
  integral_sub 只需 Integrable；AE 可测性已包含，不另需处处 Measurable。
  K/r 在 atTop 的极限已由 div_atTop 证明，不受有限点 r=0 影响。
- actual P4 错把源维度、行列 Gram 与 p 互换。所有实际函数共享 ComplexSample(m,p)
  和同一个 stdGaussian；物理 /sqrt2 在 complexSampleMatrix，没改变为复测度。
  uniform_floor 定理是 forall Z 而非 AE，故点态到积分步骤有明确支撑。
- actual P4 声称文档写“generic rank”，本模块没有该表述；这里只陈述 noiseless-surjective
  条件。固定参数退化时 delta 变小的提醒正确，已明确不作参数一致性结论。
- generic 导入范围较大是依赖整理建议，不是缺失矩阵证明；实际实例由单独模块提供。

没有按错误警报改动正确的数学声明，也不把 P4 当作独立编译或人工批准。
[需人工审查] 测度、积分线性/极限、CN1方差与物理模型及论文对应。
冻结论文/PDF/投稿包未刷新；完整 Lake/mathlib 重建 NOT_RUN。
