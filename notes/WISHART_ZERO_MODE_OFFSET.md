# 含零模态的偏移：明确对数矩假设的接口

本增量3项，不能当作一般奇异相关高斯偏移已无条件完成。
定义positiveSpectrumLog(x)=log x若x>0，否则0。

通用有限测度标量定理：f可测、L1、AE非负，且positiveSpectrumLog(f)真L1，
则 Elog(1+rf)-mu.real{f>0} log r -> EpositiveSpectrumLog(f)。
证明把测度限制到{f>0}，不归一化、不除该事件概率；零质量事件也允许。
在限制测度上应用已证log(f+1/r)积分连续性；原测度上f=0的模态没有贡献。
有限谱求和后，系数是各正谱事件概率之和。

实际固定B:p×n、M:m×n、source Z:m×p：给定每个正谱对数L1的明确hlog前提，
EC(r)-q log r -> E SUM_i positiveSpectrumLog(lambda_i)，q=min(m,rank stacked[B;M])。
q的识别复用实际AE秩公式与确定性Gram正模态数=rank，含所有零维。
这里SUM log正谱在数学上是log伪行列式，但本增量没有构造一般伪行列式多项式身份。
对任意B/M的hlog尚缺，不能仅凭rank AE常数或非零多项式零集null填补。

不同家族Qoder最终2-source P4真实返回。其具体疑虑裁决：
- gram_positive_modes_eq_rank由CorrelatedLogDetGenericRank->CorrelatedLogDetExpectedRank导入；
  明确是complexGram X=X^H X的n×n全谱（包含零模态）正计数=rank X。
- Fin(card(Fin n))是原生排序索引，无另一个需手工强转的类型。
- integral_log_one_add_mul和integral_log_add_inverse_tendsto都不要求概率测度；
  实际stdGaussian另有概率实例，常数积分=q。
- hm/hn在restrict积分等式中经AE过滤器使用，未把AE非负改成处处非负。
- actualCorrelatedMatrixLogDet_eq_spectral前提恰为r>=0，满足eventually_ge_atTop0。
- hlog明确在声明里；没有把条件结论误记为无条件成果。

数值：mixed_noiseless_offset_preflight seed202610201013，200000样本，23项；
覆盖X=[A,0;D,I]的Schur恒等式、方阵A使D项消去、已知digamma期望与r>a附加项，
零模态Exp混合的独立积分对照；不作为一般概率证明。
均值一致小球控制另见scalar-uniform-smallball-control；它的逆矩/负对数界此时仍仅控制。

[需人工审查] 限制测度/对数可积性/积分极限及物理模型。模型P4不是独立编译或人工批准。
完整Lake/mathlib重建NOT_RUN，冻结论文/PDF/投稿档案未变。
