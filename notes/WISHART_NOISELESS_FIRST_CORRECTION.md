# 实际行 Gram 偏移的首阶逆迹系数

固定 B:p×n、M:m×n、m>0，M restricted kerB 满射，X=ZB+M，W=XX^H。
沿用 W>=delta I 的同一固定正下界。令 Delta=EC(r)-m log r-ElogdetW。

已机检：所有自然数 k，实际 tr((W^-1)^k).re 真L1（含k0）；
0<=E tr(W^-1)-r Delta<=m/(2 r delta^2)，故 r Delta -> E tr(W^-1)，有限。
普通逆通过谱对角化构造真正右逆再用 Matrix.inv_eq_right_inv，未用伪逆。
标量核心为 0<=u-log(1+u)<=u^2/2，对所有u>=0，由导数非负证明，
不是把局部幂级数在整个正半轴任意延伸。没有DCT：固定谱下界使误差直接一致有界，积分后夹逼。

本增量13项包括通用逆幂谱迹、标量微积分、可测/L1和实际界，并非13个独立研究突破。
27项高精度闭式/积分控制已在证明前通过，数值不是证明。

## Qoder 协作与裁决

P1 first-correction-1013 真返回，给出三路线；采用其统一标量误差路线。
其“row-minimum singular value”说法不精确，本项目最小值始终是Gram特征值。
两个通用源码、行逆谱模块、首阶两源码各自真实最终P4均保留并审计绑定。

- inverse-taylor P4 对 eigenvalues/eigenvalues_0 的“排序缺口”是误报。
  pinned Spectrum 中 eigenvalues 定义就是 eigenvalues_0 经明确 card等价重编号，
  此处 Equiv.sum_comp 恰为该等价，没有另一个隐藏排序置换。hnz _ 同样按定义展开。
- 同份P4误读 monotoneOn_of_hasDerivWithinAt_nonneg 的变量域。
  该API导数与非负性回调明确要求 interior D，因此 interior_subset 正确，边界连续性另有hc。
- 行谱P4把 complexGram_posSemidef 的 .1 当矩阵；实际上 .1 是同一Gram的 Hermitian证明。
  不存在“两个计算结果差一个proofterm”的情形；正谱给普通逆的具体前提已匹配。
- 同份P4声称 p+m>n 时 hs 不可满足，这是错误的。约束是 rankB+m<=n，不是p+m<=n；
  例如B为100×1零矩阵，m=n=1、M=[1]即可。其正确的实际结构限制已显式保留。
- subtype_mk不要求Prop证明本身可测；Hermitian子类型使用继承的可测结构。
  m>0是逆最小值路线的明确条件，并非声称所有模块处理m0。
- 首阶P4再次猜错 complexGram方向，实际定义固定为 A^H A：X^H为n×m，其Gram为m×m。
  导入定理无额外未提供的秩/密度假设，逐样本界与谱迹重写由最终exit0核验。
  所有函数在同一 ComplexSample(m,p)源，complexSampleMatrix内物理除sqrt2；
  常数界由所有矩阵的delta下界推出，不假定CN1模型额外缩放。
- 条件可能不满足不意味着“未守卫的空真”，声明明确携带hs；B=0、M满行秩给非空实例。
  均值固定、delta先于r选取，不声称参数退化时的一致界。

[需人工审查] 谱可测性、积分线性、物理方差、ROW方向及论文模型对应。
模型P4不是人工审查或独立编译。完整Lake/mathlib未重建，冻结论文等四产物未改。
