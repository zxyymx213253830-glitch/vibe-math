# 2026-10-22 本轮成果与审查入口

截至03:17UTC，当前普通额度仍可用，工作仍在继续。最新已验收提交4f67d55，**665项审计绑定声明（663定理/实例+2构造）**，audit PASS，主入口facade72真实exit0。本轮从610增加55个打印声明、18个模块，完成8个可运行里程碑；这些声明包含通用分析和代数工具，不等于55个新的概率定律。

## 模型和主要结果

固定任意复矩形矩阵B:p-by-n、M:m-by-n，Z:m-by-p为iid proper CN(0,1)，X=ZB+M。允许奇异、零B/M和零维。记

    R=min(m,rank stacked[B;M]),
    C_r=log det(I+r X^H X),
    S=sum over strictly positive Gram eigenvalues lambda of log lambda.

对数采用自然底；S保留0<lambda<1的负对数，零模态贡献0。只研究固定参数。

| 成果 | 精确范围 | 详细审查包 |
|---|---|---|
| 精确子集Cauchy–Binet与Gram多项式系数 | 矩形、含零维，每个子集一次；Gram系数是全部对应子式的模平方和 | WISHART_EXACT_SUBSET_CAUCHY_BINET.md |
| 期望full-logdet曲率 | 正尺度F''(r)=-sum E[(lambda/(1+r lambda))²]；凹且严格凹当且仅当R>0 | WISHART_EXPECTED_LOGDET_CURVATURE.md |
| 高尺度导数极限 | rF'(r)->R，-r²F''(r)->R，未增加逆矩假设 | WISHART_SCALED_DERIVATIVE_RANK_LIMIT.md |
| 高斯多项式log平方 | 任意有限全纯复多项式在实际proper高斯源下log范数平方真可积；含总化log0=0 | WISHART_FINITE_GAUSSIAN_LOG_SQUARE.md |
| 奇异模型正谱log有限方差 | S及各个正谱log属于L2，Var(S)有限；没有一般闭式数值 | WISHART_SINGULAR_LOG_VARIANCE.md |
| 随机偏移均方收敛 | E[(C_r-Rlogr-S)²]->0；同一物理样本上比较 | WISHART_SINGULAR_OFFSET_MEAN_SQUARE.md |
| 二阶矩与方差极限 | E[(C_r-Rlogr)²]->ES²，Var(C_r)->Var(S)；r>=1实际统计量属于L2 | WISHART_SINGULAR_LOGDET_VARIANCE_LIMIT.md |

这些结论没有证明CLT、收敛速率、随均值/协方差变化的一致性，也没有从统计量推导编码容量。方差极限不能被改述成整个随机变量的高斯极限。

## 验证与合作

全部证明体由Codex编写；Qoder Qwen3.8-Max承担不同模型家族的有界路线讨论和最终源码P4。本轮8份最终源码P4真实返回，问题和误报均保留并按锁定定义/API裁决，不把模型审查当成人工批准或独立编译。

7个已验收实验脚本共403项控制检查，包含精确代数、固定种子20万样本、Gamma/闭式/独立积分/有限离散对照；多尺度使用共享样本，不能宣称403个独立实验。数值对照不是证明。另一个9例最小正谱预检仍OPEN，不计入665项。

每个接受包锁定完整源码、声明类型、依赖源码/olean、工具链、审查快照、检查器、日志和返回码；主入口串行检查和绑定审计通过。源码没有在P4后偷偷修改。早期失败的类型核对器和源码尝试日志保留；失败版本没有接受。当前有36份接受记录。

## 尚待完成

一般奇异模型的最小正特征值逆矩阈值正在预检，见WISHART_NEXT_SINGULAR_POSITIVE_INVERSE_CARD.md。一般d中央锐常数的经典简式、非中心G2、原一般T1候选行列式恒等式、T3刊版归一化及全文T1–4对应仍未闭合。

SHEAF用于依赖队列、锁定类型和验收协调，不是已经全自动替代研究员的证明器。Linux原生副本仍是先前439文件的源码/索引对照，本轮18模块没有宣称已同步；Linux独立Lean内核编译、完整Lake/mathlib构建均NOT_RUN，不能从索引速度推出证明速度提升。

**[需人工审查]** 测度、Fubini、极限/求导与积分交换、Holder、AE秩、Gaussian方差归一化、实际模型及论文对应仍需人审。形式化进展不等于已证明数学或文献新颖性。

冻结论文、PDF、arXiv上传包、代码发表包均未改动，仍是旧版本；本轮成果不应被表述成已经进入投稿包。详细证据保存在verification/sheaf_wishart/quota-20261022-0949和verification/central_mixed_moments/audit.json。
