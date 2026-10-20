# 一小时续研记录：2026-10-20 15:05–16:05 北京时间

授权窗口：07:05:09–08:05:09 UTC。用户明确要求继续一小时并合作；本轮按固定时限，
不再沿用旧的无限期耗尽额度模式。既有自动任务保持暂停，由当前单一协调者推进。
本记录的研究成果已于07:50UTC验收，后续窗口用于范围核对、证明说明和归档。
到期状态由独立summary及session state记录；不据本文标题假装已提前到期。

## 实际完成的内容

模型：Z:m×p iid CN(0,1)，两个标准实坐标除sqrt(2)；B:p×n和M:m×n任意固定，
X=ZB+M。B可奇异、矩形、零。先前只有实际期望秩形式的斜率，本轮得到确定值：

q=min(m,rank_C[B;M])
 =min(m,rank_C B+rank_C(M限制到ker B))。

- **实际通用秩**：rank_C X=q 几乎处处。先证明每个Z的上界和达到上界的确定性见证，
  再以q×q压缩多项式的非零见证与既有高斯零集定理取得AE下界。包括全部零维形状。
- **实际full-logdet斜率**：E log(Re det(I+rho X^H X))/log rho→q。
  自然对数，同一物理均值M；不是信道编码/互信息推导，也无SNR变化参数的一致性。
- **列Gram零点原子**：n>0时 P(lambda_min(X^HX)=0)=1 若q<n，否则0。
  奇异B不自动推出原子1；均值可补回噪声缺失方向。m=0,n>0时为1，n=0最小值不定义。
- **无噪声均值撑满输出的边界**：m>0且rank(M|kerB)=m时，存在固定C使BC=0、MC=I。
  每个Z都有XC=I，故行Gram XX^H 的最小值有与Z无关的正下界δ。实际行最小值
  所有非负实数阶逆矩均L1。此处必须区分行Gram与可能恒奇异的列Gram。

两个可直观核对的例子：B=[1,0]。m=2、M第二列=(0,1)^T时，X的行列式等于
第一个复高斯坐标，所以几乎处处列满秩；m=1、M=[0,1]时，行Gram=|z|²+1≥1，
而2×2列Gram始终有一个零特征值。两者都被通用结论覆盖。

## 机检与合作

起点491项，终点515项（513定理/实例+2早前构造）；新增24个打印声明，8个模块。
计数含纯代数、谱桥和可积性辅助，**不是24个独立概率突破**。所有新证明体Codex。

| 新模块 | 新声明数 | 最终叶日志 |
|---|---:|---|
| CorrelatedRankUpperBound | 3 | rank-upper-0705-3 |
| CorrelatedRankWitness | 2 | rank-witness-0705-2 |
| MatrixRankCompression | 1 | rank-compression-0705-2 |
| CorrelatedGaussianGenericRank | 4 | gaussian-generic-rank-0705-4 |
| CorrelatedLogDetGenericRank | 3 | logdet-generic-rank-0705-2 |
| CorrelatedMinimumZeroAtom | 5 | minimum-zero-atom-0705-1 |
| CorrelatedNoiselessSpectralFloor | 4 | noiseless-floor-0705-3 |
| CorrelatedNoiselessInverseMoments | 2 | noiseless-inverse-0705-1 |

所有最终叶子退出0，仅propext/Classical.choice/Quot.sound；最终绑定审计PASS。
主入口facade46（509项）退出0；facade47（515项）曾空日志异常退出，原因未确认，
未删日志或伪称通过。同源码、同串行gate、相同参数重检facade48真实退出0，独立receipt
保留开始/结束/退出码/日志哈希。日志中的旧ring尝试提示是已有证明的信息输出，
不据文本提示改判真实成功退出码。完整Lake/mathlib构建仍NOT_RUN。

真实Qoder调用8次：2次P1、6组最终源码P4，全部有真实回复且退出0；工具/MCP关闭。
请求模型Qwen3.8-Max，报告qmodel_38max，未独立核实供应商模型权重。Qoder不写证明体，
也未独立编译。多处均值抵消、源中心、域/值域、Measure.real、维数与倒数方向警报
有错误，原回复和逐项裁决全部保存。不得将“收到审查回复”表述为全面批准/人工审查通过。

## 可复现前检

- 64个精确有理复数方阵压缩：LX0H=I，含零秩、源坐标恢复及错误完整Gram见证负控制。
- 均值恢复/退化零模的精确小例：同时检测“奇异B必有零最小值”和“秩处处达到上界”的错误。
- 35个固定无噪声右逆/谱下界精确实例，保守Frobenius下界与全部主子式核对。
- 下一偏移卡的标量前检：seed202610200705，200000个实际CN1样本；能量/谱矩、
  逆阶0.5/1/2/5/20、5个rho的full-logdet与独立闭式/积分一致。15项通过。
  标量E[log(1+Exp1)]=E[1/(1+Exp1)]=eE1(1)≈0.5963473623231946。

前检只是实现控制/数值证据；任意B/M结论来自上述最终Lean证明，不来自有限样本。

## 发表与后续边界

核心里程碑提交a48cdb6；谱下界/逆矩里程碑6bac414。没有远端推送。
冻结main.tex、PDF、arXiv上传ZIP与代码ZIP的四个SHA256逐项保持旧值，未更新论文或投稿。
新成果的完整参数、证明路线、审查裁决分别见WISHART_GENERIC_RANK.md和
WISHART_NOISELESS_SPECTRAL_FLOOR.md。

下一张具体卡：WISHART_NEXT_NOISELESS_OFFSET_CARD.md。
窗口末与Qoder核对了更短的C(1)减去有界误差路线，优先推进；仍只是后续路线，未计新声明。
无噪声撑满条件下的一般实际行logdet偏移和rho倍误差首项仍开放，仅标量前检通过。
更一般的奇异相关逆矩阈值、非中心最小值显式CDF/PDF、联合G2、原一般T1行列式候选恒等式、
一般d简化硬边常数、T3刊版归一化解释及完整原T1–4对应仍开放。

[需人工审查] 非零多项式零集/Fubini、高斯绝对连续性与复方差、AE/DCT、算子范数/
谱/矩形模型方向、论文物理参数对应和证明文本人工审查。模型P4不替代这些义务。

## 到期关闭

2026-10-20 08:05UTC窗口到期，session与独立summary已写CLOSED_USER_ONE_HOUR，
自动任务已通过工具确认PAUSED。没有本任务检查/审查进程残留，也没有compute锁。
08:02UTC普通额度仍可用（primary48%、weekly8%已用），本轮按用户固定一小时结束，
不是额度耗尽。到期后仅保存归档，不再启动数学/机检/模型请求。等待用户明确恢复。
