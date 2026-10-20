# 下一张卡：无噪声撑满情形的行 Gram 偏移与误差 — OPEN

固定B:p×n、M:m×n，m>0，s=rank(M|kerB)=m，X=ZB+M。
本轮已证：固定δ>0使对所有Z，lambda_min(XX^H)≥δ；实际最小值所有p≥0逆矩L1。
一般任意B/M通用秩与full-logdet斜率也已证，但本卡要求更强的偏移结论。

## 优先短路线：先由C(1)推出logdet可积，暂不建逐谱积分接口

本轮末提出并交Qoder P1核对（`p1-noiseless-offset-short-route-0705`），得到真实回复。
令ell=log(Re det W)，W=XX^H。先逐点证
e_r=C(r)-m log r-ell=SUM log(1+1/(r lambda_i))，0≤e_r≤m/(rδ)。
在r=1，ell=C(1)-e_1。ell由实际矩阵det与总定义Real.log可测，e_1有界且可测，
C(1)已真L1，故直接推出ell真L1。再积分同一误差界，得到偏移极限和O(1/r)界。
这样无须先构造每个行特征值的L1/logL1。下面逐谱路线作为备选，不再首选。
所需源接口已经定位：`CorrelatedLogDetLowScale.integrable_actualCorrelatedMatrixLogDet`
（r=1）、`HermitianSpectralLogDet.hermitian_real_logdet_eq_sum_log`、
`.gram_real_logdet_eq_spectral`，以及已闭合的标量log_inverse_error_bound。
有界支配用已知integrable_const.mono'，不要直接采纳未经核实的API猜名。

P1确认该数学路线在固定δ>0、概率测度、ROW方向下成立；这不是Lean新证明或P4。
其“谱误差界已经机检完成”的措辞过强：本轮完成的是δ谱下界，e_r身份/上界仍待写。
其n>m也不是必须，n=m、B=0、M可逆仍符合条件；只在n>m时列Gram必奇异。
它猜测的Matrix.log_det/Integrable.of_bounded未采用。首阶逆矩阵trace系数仍单列待补。

下一目标，当前没有新证明源码：

1. 实际 log det(XX^H) 绝对可积；
2. EC(rho)-m log rho → Elogdet(XX^H)；
3. Delta(rho)=EC(rho)-m log rho-Elogdet(XX^H)非负，
   Delta≤m/(rho δ)，且rho Delta→E tr((XX^H)^(-1))，有限。

必须使用 m×m 行 Gram；列 Gram 若n>m恒有零特征值，不能取其普通logdet偏移。
这里B/M固定，δ可以依赖它们，不声称随SNR退化参数的一致结论。

## 锁定资产与实际待补步骤

- `CorrelatedNoiselessSpectralFloor.correlated_rowGram_uniform_floor` 与
  `CorrelatedNoiselessInverseMoments.actualCorrelatedRow_inverseMoment_integrable_of_noiseless_surjective`。
- 实际行谱函数取 complexGram(X^H)=XX^H 的有序特征值，源始终同一m×p Gaussian。
  不需要也不能未经证明将相关模型当作iid转置模型。
- `CorrelatedGramTraceMoments` 已有实际迹L1；traceXX^H=traceX^HX 用矩形trace乘法交换。
  用0≤lambda_i≤traceXX^H取得各行谱L1；可测性从Gram/有序Hermitian谱连续性取得。
- 下界δ给lambda_i≥δ>0、各逆一阶L1。搜索并复用 `LogMomentIntegrability` 的
  正谱+逆分数矩到logL1接口，不重做DCT。
- `FiniteSpectrumLogDetGrowth.integral_finiteSpectrumLogDet_offset_tendsto` 精确要求
  每个谱L1、AE正和logL1；索引大小m。它给有限谱和偏移，尚要接到实际行det。
- `LogDetOffsetIdentity.finiteSpectrumLogDet_offset_error`、
  `LogDetErrorBounds.integral_log_inverse_error_bounds` 与
  `.integral_log_inverse_error_first_order` 给误差桥。常数δ支配给显式m/(rhoδ)。
- 通过Sylvester `Matrix.det_one_add_mul_comm` 同一样本上比较列/行full-logdet，
  类似 `GramLogDetTranspose.det_one_add_gram_transpose`。避免不必要的源测度重排。
- 终点E sum inverse eigen应另接实际逆矩阵trace，不能默认数值算法的伪逆就是逆。

## 已通过但不作证明的前检

`experiments/noiseless_row_logdet_offset_preflight.py`，seed202610200705，200000样本。
模型m=p=1,n=2，B=[1,0]，M=[0,1]，lambda=1+|CN1|²。
已知闭式Eloglambda=E1/lambda=e E1(1)，用独立quad对照。
EC(rho)=log(1+rho)+exp(1+1/rho)E1(1+1/rho)，检查rho0.1,1,10,100,1000。
另核对CN1能量均值、行谱一/二矩、逆p=0.5,1,2,5,20、Sylvester矩阵行列式和
0≤rho log(1+1/(rho lambda))≤1/lambda。15项全部通过；不是一般偏移证明。

[需人工审查] 同一样本的谱/行Gram/物理方向、可测性、积分交换、极限支配与方差。
P4必须不同模型家族，提交实际最终完整源码，保留错误警报与裁决。冻结论文不刷新。
