# Wishart 形式化：滚动状态

更新：2026-10-15。本页是当前交接入口；历史按小时笔记保留作证据，不再另建同类状态页。

## 已核验的实际模型结果

| 范围 | 当前结果 | 证据与边界 |
|---|---|---|
| T1/T2 单列 | 非中心 1×1、任意均值 2×1、参数匹配/直接 Frobenius 参数的 3×1；中心任意行单列 | 现有 tracker 中的实际模型声明；不是一般多列定理 |
| 中央复 2×2 | 严格尾 `P(min>x)=exp(-2x)`；CDF `1-exp(-2x)`（x≥0），负域 CDF=0；实际推前 `expMeasure 2` | `TwoRowMinimumLaw.lean`，原六声明标准三公理；注意 exp(-2x) 是尾概率，不是 CDF |
| T1 中央复 2×2 | 原 `theorem1CdfCandidate 2 2 0` 等于实际最小 CDF | `Theorem1CentralTwoRowActualCDF.lean` 五声明；原候选与常数未改 |
| 实际尺度 | `min(Gram(X(a z)))=a² min(Gram(X(z)))`；a>0 时实际最小律 `Exp(rate=2/a²)`；v>0 用 a=√v | `TwoRowScaledMinimum.lean` 十声明标准三公理；标量协方差 vI，非任意协方差 |
| T4 | 任意均值、任意正行数单列 CDF 首项 | `T4NoncentralOneColumnAnyRows.lean`；多列/密度一般渐近仍开放 |

2026-10-15 验收：缩放律叶子和包含它的主 facade 均退出 0。当前完整 `lake build` 未运行，不能与主入口检查混称。新源码严格 UTF-8 解码通过，无 U+FFFD；终端显示乱码不等于文件损坏。

作者来源：Codex 写实际概率与谱桥；本地 `deepseek-prover-v2:7b` 提供短样本矩阵缩放证明，原始 tactics 保留，标 `GUIDED_COLLABORATION`。本地输出是经内核筛选的证明工具结果，不承担路线判断。旧 determinant helper 也仅为代数辅助。

## T3：先裁决，不写概率桥

- 旧本地转录 bug（c3 把分母误乘）已于 10 月 9 日修复，不能再次算新发现。
- `T3CentralNormalizationClosure.lean` 已有严格反例：源转录候选在 `(s,t,L,k,x)=(2,3,0,2,2)` 大于 1，故不等于任何事件概率。这只针对当前转录，不是刊版定理已被证伪。
- 原秩一百万样本证据已在旧审计，10 月 15 日独立复核使用 seed=20261015，每个 λ 的 200000 个实际 CN(0,1) 3×4 样本。中央/非中心迹分布控制通过；Bessel 与 0F1 两套积分实现逐列交叉核对。
- λ=1,x=1：实际 `0.009510`，显示 `0.019397228`，除 `Γ₂(3)=2` 后 `0.009698614`。λ=2 和多个阈值也支持同一残留因子。x=0.5 的稀有事件不全部达到 8SE 分离，不隐去这一分辨率限制。
- 复现：`experiments/t3_rank_one_partition_audit.py`；结果 `verification/WISHART_T3_RANK_ONE_AUDIT_20261015.json`。初版误要求所有稀有阈值均达 8SE，被纠正为事先选定可分辨阈值 x≥1；固定种子未变。数值不是证明。
- 来源复核：arXiv v2 HTML (17),(21),(24)–(26),(64)–(68) 的显示式与本次计算一致。来源：[arXiv v2](https://arxiv.org/html/cs/0611007v2)。刊版/勘误、隐含列规范和有序域引理解释仍待人工核对。保持 `displayed_c3` 和 `derived_c3` 分名，不悄改论文候选。

## P1 路线比较与选择

共同隐含条件：单位复方差、正确的小侧 s×s Gram、0<s≤t 整数、实际尾概率应用的阈值 x≥0、实维 s² 的 Hermitian 坐标测度、PD/PSD 边界零测、可测事件、可积性与 Tonelli/Fubini、平移保持同一坐标体积。不能在全部复矩阵的 2s² 维 Lebesgue 测度上积分 Hermitian 子集，否则会得到零测/空洞结果。

| 路线 | 最少关键引理 | 对应经典结构/已有资产 | 风险与机检方式 |
|---|---|---|---|
| A 中央矩阵密度 + PSD 锥平移 | 实际 Gaussian→Hermitian Wishart 密度；平移体积不变；trace 平移；det(V+xI) 的有限矩 | 复矩阵 Gamma/Wishart 密度；现有中央 2×2 实际 Gram 密度、平移锥证明 | 避开谱 Jacobian，但矩阵密度仍须从真实 Gaussian 推导，不能作为新假设。代数 Lean；密度/换元 `[需人工审查]` |
| B 通用 Bartlett/Cholesky 归纳 | 各步投影/残差的 Gamma 与 CN 条件律；联合独立；通用三角→Hermitian Jacobian | 已有任意 m 的投影/残差独立，只有特定残差能量律已闭合 | 选可测基/条件分布、零对角例外、π 和 2 的体积因子；Lean 概率桥 + 固定 seed 控制；不可每维再做孤立 chart |
| C 一般有序联合谱密度 G2 | Hermitian→谱/酉轨道 Jacobian；酉积分；非中心矩阵特殊函数；重根与归一化 | 已有谱连续/简单谱/阈值无原子、Andréief 代数 | 中央也需 Weyl 体积，非中心还需酉群积分；隐含假设最多。只做来源可查路线，不编造缺失库资产 |

**选择 A，B 作为一次性通用密度基础，C 留给一般非中心目标。** 中央情形不应等待一般非中心 G2，但 A 不自动关闭 T2/T3/非中心结论。

目标公式（未声称一般情形已证）：坐标密度应为 PD 锥上的 `K det(W)^(t-s) exp(-tr W)`，`K=1/(π^(s(s-1)/2) ∏_{j=1}^s (t-j)!)`。对 x≥0，平移给出 `exp(-s*x) K ∫_{V≻0} det(V+xI)^(t-s) exp(-tr V)dV`。t=s 时仅在实际矩阵密度/质量已核验后，才能推出 `P(min>x)=exp(-s*x)`。t>s 时还需要有限矩计算，不能丢掉 det 因子。已证的纯核积分恒等式允许负 x，但此时平移锥不再包含于实际 PD 支撑，不能丢掉额外支撑指标并当作尾概率。

下一张核心卡：固定全维 Hermitian 实坐标和通用 Cholesky 递推，证明维数无关的 Gaussian→矩阵密度归纳一步；先列清 Jacobian 的行列式幂/对角平方根，再证明实际概率。若暂时只能完成确定性平移/核恒等式，明确记为确定性资产，不计一般概率突破。

## 审查分工

P4 不再交给本地 DS。它先前的重复无关回应、错事件和占位符已归档，均不算审查通过。由 Claude/用户进行跨家族审查；准备的审查包不等于已完成审查。

优先：2×1 换元/球面积分/Fubini/均值方向；中央 2×2 Bartlett 条件独立、复到实与 Gram Jacobian、零边界、方差和严格/弱谱事件；随后 3×1。所有这些仍标 `[需人工审查]`。

## 本窗口简记

20:35:38–21:35:38：补归档旧 T1 中央 2×2；提交缩放律并主入口 PASS；按用户新方向停 SER，完成独立 T3 秩一核对，收敛到本滚动页。旧窗口只读，不延长当前截止。临时文件按用户点名精确加入 `.gitignore`，保留文件本体；未知草稿不删除、不暂存。

21:13 路线里程碑：任意 n 的严格谱阈值与 trace/核平移、任意 m/n 的分块合同因子/行列式/正定等价、n² 实坐标与 Hermitian 子空间的可测等价均已叶子核验标准三公理。坐标体积显式为 n² 个实 Lebesgue 的乘积推前；不使用全部复矩阵的体积。它们是通用确定性/坐标资产，不是一般实际 Wishart 概率律；候选核锥积分平移还在处理 Pi 测度不变性接口。

21:15：通用候选核锥积分平移三声明 PASS 标准三公理。矩阵密度尚未由真实 Gaussian 推导，因而没有一般概率结论。Pi 坐标测度的加法不变性用锁定库 `Measure.pi.isAddRightInvariant` 明确构造，所有失败反馈保留。正在做含通用模块的主入口检查。

21:17：含通用锥积分/分块/实坐标的主 facade 检查退出0；全量源码词法扫描（跳过注释和字符串）无真正 sorry/admit/axiom/native_decide，150顶层叶模块/160含生成子模块，另1主入口。完整 Lake 构建未运行。P4 manifest已刷新，仍仅待审包；DOI及刊版PDF访问失败，不据arXiv数值断言刊版错误。

21:25：`GaussianOrthogonalProjectionLaw` 四声明叶子 PASS：实际 Gaussian 经 coisometry/固定子空间正交投影后的完整律，以及实维 2k 子空间的半范数平方 Gamma(k,1) 律；直接复用既有径向 Gamma 资产。它是固定子空间的实际概率律，尚不是随机 QR 条件律或一般 Wishart 密度。`--projection-only` 的 200000 Gaussian/χ² 控制通过；`--block-jacobian-only` 精确验证残余维 n=1,2,3 的绝对 Jacobian r^n，符号依坐标顺序；这三个有限维符号控制不代替一般 Lean 证明。

## 下一核心卡：真实中央矩阵密度，禁止以目标密度为前提

参数：整数 `0<s≤t`。样本为现有 `ComplexSample (m:=t) (n:=s)`，复矩阵条目 `/sqrt 2`。目标是实际 `realCoordinatesOfHermitian ∘ complexSampleGram` 的推前律等于选定 `hermitianRealCoordinateMeasure s` 上的 PD 锥密度：

`1/(π^(s(s-1)/2) ∏_{j=1}^s (t-j)!) · det(W)^(t-s) · exp(-tr W)`。

这是待证目标，不是新增 `hDensity` 前提。已知的 Gaussian 原始坐标密度、固定子空间投影/Gamma 律、通用分块合同式、Hermitian 坐标等价和锥积分平移均应复用。

归纳一步按四个独立义务验收：

1. **条件律**：固定已取列空间后，残余列在其正交补上仍为独立标准复 Gaussian；再用已证固定子空间律。要证明参数化投影及残余 Gram 可测，并由 Fubini/概率核连接随机先前列，不能直接把“固定”换成“随机”。可用 Gram 矩阵逆的显式投影，避免未经证明的全局可测 QR 基选择。
2. **一次性一般 Jacobian**：r>0、z∈ℂ^(s-1)、B 为低维 Hermitian，映射 `W=[[r,√r z*],[√r z,B+zz*]]` 在明确实坐标下绝对 Jacobian 为 `r^(s-1)`。目前仅小维符号控制；需维数无关的导数块三角证明。通用 `centralBlockStep_factor/det/posDef_iff` 是几何输入，不是假定 Jacobian。
3. **归一化与指数**：`det W=r det B`、`tr W=r+‖z‖²+tr B`；密度幂加 Jacobian 后，r 的幂为 `(t-s)+(s-1)=t-1`。常数必须满足 `K(s,t)=K(s-1,t-1)/(π^(s-1)(t-1)!)`，并对 s=1 的既有 Gamma 律核验；不得借 T3 争议常数代替该归纳。
4. **异常集与最终实际律**：复用全局阈值无原子/满秩控制排除零首能量与边界；先证真实坐标律，最后才调用锥积分资产。测度、条件化和方差均 `[需人工审查]`。

这张卡完成前，方阵一般 `Exp(rate=s)` 仍只是已获数值支持的预期结论；不能把已证候选核积分的质量自行设成 1。一般非中心 G2 和原 T3 概率桥继续保持开放。

21:27：新增固定子空间 Gaussian/Gamma 实际律与通用路线一并加入主入口，检查退出0。下一卡已明确真实中央矩阵密度的条件律/Jacobian/归一化/异常集四项义务；实际尾应用明确 x≥0。当前完整构建未运行，独立P4仍待Claude/用户。
