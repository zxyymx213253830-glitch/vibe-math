# 下一卡：跨Gram尺寸的最小正值输运（OPEN）

675检查点后，固定共同核等距压缩及固定可测AE最小正坐标已完成，勿重写。一般奇异逆矩阈值仍OPEN。

已有资产：

- CorrelatedFixedKernelCompression为固定B,M给出s=rank stacked[B;M]、n-by-s C，C^H C=I，B C C^H=B，M C C^H=M，并对每个Z精确保持行Gram。
- FixedRankPositiveMinimum在R=min(m,s)>0时给出固定排序指标R-1，可测，AE为最小严格正特征值。
- GramSpectrumTransfer的roots_count_eq_of_ne_zero已证明两Gram方向任意非零根重数相同（给定尺寸次序；另一分支对共轭转置使用）。
- 锁定mathlib Analysis/Matrix/Spectrum.lean的roots_charpoly_eq_eigenvalues₀可把Hermitian特征根成员关系翻成有序坐标。

## 优先目标

1. 对任意x>0，证明x是X列Gram的某个有序特征值，当且仅当x是X^H的列Gram某个有序特征值。先复用非零根重数，不新建整个奇异值/minmax理论；尺寸分支必须含m=0或n=0的空存在情形。
2. 推出任意X:m-by-n和Y:m-by-r若X X^H=Y Y^H，则其正特征值成员集合相同。只需成员集合就足够比较最小值，不必重新证明重数定理。
3. 若给定X/Y中的两个坐标均严格正且各自不大于任何正坐标，用双方成员对应和反对称性证明它们相等。此确定性桥不应偷偷要求满秩。
4. 用新固定C构造恢复恒等式，证明rank(stacked[B C;M C])=rank(stacked[B;M])（rank乘积上下界即可）；随后在同一个原始2mp实高斯源上，应用两次已验收AE最小正坐标结论和逐样本行Gram等式，证明压缩前后选定坐标AE相同。n和s不同，但源宽p不变，不能误换高斯源。

控制优先复用已存固定核压缩的精确投影/行Gram/正谱参考，并补零维、秩亏及重复正特征值的跨尺寸精确对角矩阵控制。已有有限序列枚举不是一般矩阵输运证明；新增实验应在新命题证明前运行。

下一步才做canonical块谱最小值、噪声酉投影/独立law、fixedmean wide逆矩输运和双向临界ENNReal桥。ZBC通常不是iid标准噪声；保持谱不等于已白化分布。

[需人工审查] 后续谱/实际law/AE/积分与模型。该卡无新Lean证明，不计新增项；冻结发表产物/fullLake/Linux独立内核边界保持。
