# 下一卡：canonical无噪声块与Gaussian正规形（OPEN）

680检查点后，固定共同核等距压缩、可测AE最小正坐标、跨尺寸正谱成员和实际压缩前后AE最小正值等同均已完成，勿重复。一般奇异逆矩阈值仍未完成。

固定压缩后列数s=rank stacked[B;M]，共同核为0；b=rank B，c=rank(M restricted ker B)，s=b+c。预期在固定可逆列变换和固定酉行变换后得到

    D=[[A,0],[H,N]],   a=m-c>0,

其中A:a-by-b、H:c-by-b为独立proper Gaussian块加固定均值，N:c-by-c固定可逆。这是尚需形式化的正规形/law，不是已证明结论；b=0或c=m的全逆矩有限分支应单独处理。

## 可以先推进的确定性谱卡

1. 对E=diag(A,N)，复用分块charpoly乘积/根成员，证明正谱是两块正谱并。不要重新证明一般Hermitian排序或SVD。若两块有正值，最小正值为两块最小正值的min；空块或rank0块只取非空正谱块，不能把总化log0或最小值0混进来。
2. S=[[I,0],[-N^-1H,I]]满足DS=E，逆只换符号。已有singular_block_shear_control.py的20例81项控制可复用；若新增子命题，再补对应精确/已知参考对照。一般范数可取1+||N^-1H||，矩阵维数重索引及Euclidean块范数要显式。
3. a>=b且A列满秩AE时，对DS用既有右因子普通Gram最小值比较；a<b且A行满秩AE时，对E^H=S^H D^H用既有左比较。原普通列最小值可能是0，必须用680已验收的正谱输运桥，不能省去共轭转置。

## 正规形/law路线

可考虑ker B正交补和range B的固定正交基，构造B在正交补到其range的线性等价并取逆，再把range的正交基包含到噪声源；这样无需假设锁定mathlib有完整SVD API。可复用FixedKernelCompression、已有GaussianOrthogonalProjectionLaw与CorrelatedRankWitness的补空间见证思路，但需逐条检查精确类型。

固定列变换不是酉，必须追踪正谱比较常数；保标准Gaussian的是噪声源range上的等距/酉映射。行酉投影后的A/H独立还要证明，固定均值只平移，并不让高斯块失去独立性。不能把谱压缩相等当成ZBC已经iid。

进入新主要路线前可给Qoder一个有界P1精确假设/路线分化任务；Codex写证明，最终源码另做不同模型P4。若先做确定性谱卡，明确它没有关闭分布桥。

随后才用旧固定均值tall/wide逆矩阈值，经剪切多项式因子充分性、独立有界H事件必要性，完成临界ENNReal TOP和实际源输运。所有新阈值内容仍OPEN。

[需人工审查] Gaussian方差/酉投影/独立性/AE/积分和物理模型；冻结发表产物/fullLake/Linux独立内核边界保持。此卡无新Lean证明，不计新增项。
