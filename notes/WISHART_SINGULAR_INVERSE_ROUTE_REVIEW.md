# 一般奇异最小正谱逆矩：P4裁决与实施分解（仍OPEN）

2026-10-22。补充WISHART_NEXT_SINGULAR_POSITIVE_INVERSE_CARD.md；该原卡/实验已作哈希快照，本文件不回写其内容。仍665已接受项，无新Lean证明。

Qoder第二次真实调用是路线P4（03:20:57至03:21:45UTC，exit0，Qwen3.8-Max）。它确认剪切比较的同秩序号、平方指数、独立块论证、分支及固定变换常数没有发现数学矛盾；指出两项待补依赖：分块对角正谱合并引理和wide模型的既有逆矩定理衔接。它没有批准一般阈值，也没有独立编译。响应和请求哈希保留在run目录。

## 已有定理确实给什么

已检查锁定项目源NoncentralInverseMinimumRealMoments.lean：
`actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff(m,n,hn,hnm,M,s,hs)`
适用于n>0、n<=m的实际m-by-n高斯加固定均值，目标是**普通列Gram最小值**的逆s次幂真可积，当且仅当s<m-n+1；不是一个一般wide或一般“最小正谱”定理。

若投影块A有a=m-c>0行、b>0列，a<b时应使用A^H:b-by-a，取旧定理m=b,n=a，并证明其列Gram=AA^H。该列Gram按已有固定均值满列秩AE结论正定，因此普通最小值就是其最小正谱。还要证明AA^H与A^H A非零谱相同，以及共轭转置高斯源的law；旧full-logdet转置恒等式不能单独替代这两个依赖。P4此项是合理的依赖提醒，不是已完成衔接。

## 一般模型的固定变换不可省略

固定n-by-n可逆列变换T先把B变为[U,0]，U:p-by-b列正交归一；可从B的SVD及非零奇异值缩放构造，不把T误称酉。再在ker B对应列内选基，把固定M的这部分变为[N0,0]，N0:m-by-c列满秩。固定酉行变换把range N0送到底部c维，得到

    Urow (ZB+M) T = [ [[A,0],[H,N]], extra_zero_columns ],

其中N:c-by-c固定可逆，A:(m-c)-by-b，H:c-by-b。T实际大小是n-by-n；不是只写一个(b+c)-by-(b+c)变换后跳过n-b-c个零列。删除这些零列保持非零奇异值，但也需证明。

因为U列等距、Urow酉，变换后的噪声active b列仍proper iid Gaussian；A与H为不同行投影，互相独立，固定均值只作平移。此处是一条需要形式化的分布陈述，不能从固定M的任意耦合凭空推得，也不能把任意非酉行变换当成保Gaussian方差。

## 确定性比较的精确目标

取D=[[A,0],[H,N]]，K=N^-1 H，S=[[I,0],[-K,I]]，E=diag(A,N)。DS=E，S^-1只改变K的符号；对Euclidean乘积范数，||S||与||S^-1||均<=1+||K||。

对任意秩r>0矩阵Y及方阵可逆T，需要证明同秩最小正奇异值的乘积比较

    s_r(Y)/||T^-1|| <= s_r(YT) <= ||T|| s_r(Y).

不能直接用普通列Gram最小值：wide时它等于0。对r=rank A+c，同秩比较给

    lambdaPlus(E)/(1+||K||)^2 <= lambdaPlus(D)
      <= lambdaPlus(E)*(1+||K||)^2.

E的正谱为两块正谱的多重集并。若rank A>0且c>0，则lambdaPlus(E)=min(lambdaPlus(A),sigmaMin(N)^2)；c=0时只取A；rank A=0,c>0时只取N。原候选概率分支a,b>0有rank A=min(a,b)>0 AE，但**确定性引理不能省略rank A=0分支**。数值脚本已比较同秩D/E并包含A=0；它没有证明一般多重集谱分解。

[需人工审查] 可用Courant–Fischer/min–max或秩逼近数证明乘积比较。锁定mathlib的Analysis/InnerProductSpace/SingularValues.lean目前提供线性映射奇异值定义、平方谱对应、排序、正支集等于rank前缀，未在该文件发现可直接套用的复合奇异值比较。要先完成有限维工具，不应在后续概率定理中假设这条比较“已由mathlib支持”。

## 两个积分方向

充分性：lambdaPlus(D)^(-s)至多为(1+||K||)^(2s)乘max(lambdaPlus(A)^(-s),constant)。独立时可用非负乘积积分及Gaussian全部范数矩；也可用Holder选q>1且sq<kappa，严格阈值以下可行。该替代路线不自动覆盖临界发散。

必要性：在独立事件||H||<=L上，剪切因子由固定常数控制且事件概率严格正。lambdaPlus(D)<=constant*lambdaPlus(A)给逆矩下界；旧A的临界/高阶ENNReal TOP传递给D。需用非负积分严格证明，不能把“无穷期望”代入总化实积分乘法。Gaussian块满支撑给某个足够大L的正概率即可，不必要求L任意小。

数学路线当前未发现反例，但上述代数、谱、law、独立性、可测最小正谱、积分桥均未在本卡形式化。下一张Lean卡应先选**确定性同秩乘积比较或分块对角谱合并**；不能直接宣布一般奇异逆矩阈值闭合。
