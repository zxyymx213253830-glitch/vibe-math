# 下一张卡：无噪声撑满情形的行 Gram 偏移与误差 — OPEN

固定B:p×n、M:m×n，m>0，s=rank(M|kerB)=m，X=ZB+M。
本轮已证：固定δ>0使对所有Z，lambda_min(XX^H)≥δ；实际最小值所有p≥0逆矩L1。
一般任意B/M通用秩与full-logdet斜率也已证，但本卡要求更强的偏移结论。

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
