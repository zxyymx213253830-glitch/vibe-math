# 实际行 Gram logdet 偏移的二阶逆迹系数

固定B/M、m>0、rank(M restricted kerB)=m，W=(ZB+M)(ZB+M)^H。
Delta=EC(r)-m log r-ElogdetW，I1=EtrW^-1，I2=Etr((W^-1)^2)。
此前已证ell、I1、I2绝对可积，固定delta>0给所有样本W>=deltaI。

本增量已机检：对同一固定delta、所有r>0，
0<=r^2 Delta-r I1+I2/2<=m/(3r delta^3)。
于是 r^2 Delta-r I1 -> -I2/2。
等价地 Delta=I1/r-I2/(2r^2)+R，0<=R<=m/(3r^3 delta^3)。
I2为trace of inverse square，不是square of trace inverse。ROW普通逆，不是列伪逆。
不声称参数随r变化或delta退化时的一致渐近。

标量基础为全正半轴 0<=log(1+u)-u+u^2/2<=u^3/3，
导数非负证明，无幂级数半径外使用；乘r^2后逐谱求和。
实际证明先建立误差、逆一阶迹、逆二阶迹L1，再积分线性与固定常数夹逼。
不通过DCT交换极限，也无额外随机转置/特征向量选择。
新增5项含3个确定性辅助和2个实际界/极限，连同本轮此前24项共29个打印声明。
这是标准谱微积分在已证结构下的形式化，不宣称新的经典概率公式。

## 最终 Qoder P4

两份最终完整源码、明确固定依赖契约、原始响应与receipt均绑定审计。
原始问题保留，逐条裁决：

1. eigenvalues_0原生索引就是Fin(card(Fin m))，不是另一个未经运输的索引。
   finiteSpectrum helper的l由类型推断，hf作为floor证明传入，并非把hf作为谱函数。
2/5. rowLogDet_offset_error_identity的精确假设本来就是X^H的Gram最小值；
   complexGram X^H=XX^H，已由固定定义/真实编译匹配。没有静默转置。
3. k2定理明确输出trace((A^-1)^2)，不是(trace A^-1)^2；rw不可能静默改成错误表达式。
4. 最小值比较显式调用已证orderedEigenvalue定理，排序由其antitone证明支撑。
6. 所有样本floor是确定性forallZ。将点态界积分不需要把“floor证明”当额外随机函数选择。
7. 通用积分界允许L=0,c=0，没有非零或不同函数前提，F是被积误差。没有零分母。
8. convert/ring的符号代数由kernel核验；最后极限确为-I2/2，正余项趋0。
9. 本路线只积分每个固定r的误差，再用确定性实函数夹逼；不换极限和积分，
   无需额外统一可积性定理。固定delta在forallr外选取。
10. 本模块直接积分三项L1函数，未进行有限谱积分交换；谱求和只在确定性界中。

[需人工审查] 测度、可积/线性、谱与物理CN1方差、论文对应仍需人工检查。
模型P4不等于独立编译或人工批准。完整Lake/mathlib构建NOT_RUN，冻结论文与投稿包不改。
