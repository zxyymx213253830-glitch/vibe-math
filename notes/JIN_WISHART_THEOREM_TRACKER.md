2026-10-20 10:54UTC 当前增量：547审计绑定项（545 theorem/instance+2构造），audit PASS，facade52真实exit0。新增含零模态的有限测度偏移工具及实际任意固定B/M条件偏移：hlog正谱对数L1是显式前提，尚未对一般奇异模型证明。下一关键卡为非零全纯高斯多项式负对数矩，WISHART_NEXT_GAUSSIAN_POLYNOMIAL_LOG_CARD.md；新P1超时，不计有效审查。最终两源码P4真实返回；混合块23/标量58控制通过但不作证明。固定截止11:13:42UTC，heartbeatPAUSED，冻结产物/完整构建/人工审查边界不变。

2026-10-20 10:42UTC 当前增量：544审计绑定项（542 theorem/instance+2构造），audit PASS，facade51真实exit0。固定无噪声撑满条件下二阶偏移系数已闭合：0<=rho^2Delta-rhoI1+I2/2<=m/(3rho delta^3)，故rho^2Delta-rhoI1->-I2/2，I2=Etrace((W^-1)^2)真L1。详见 WISHART_NOISELESS_SECOND_CORRECTION.md。最终两源码Qoder P4真实返回、误报逐条裁决；一般秩亏模型的偏移仍OPEN。截止11:13:42UTC/heartbeatPAUSED；冻结论文/完整构建/人工审查边界不变。

2026-10-20 10:38UTC 当前增量：539审计绑定项（537 theorem/instance+2构造），audit PASS，facade50真实exit0。固定无噪声撑满模型下普通行Gram逆迹幂全体自然阶真L1；rho Delta->Etr(W^-1)，且0<=Etr(W^-1)-rhoDelta<=m/(2rho delta^2)。详见 WISHART_NOISELESS_FIRST_CORRECTION.md。三份最终P4真实返回、误报已裁决；二阶系数尚未纳入审计。固定截止11:13:42UTC，heartbeatPAUSED；人工审查/冻结产物/完整构建边界不变。

2026-10-20 10:27UTC 当前增量：526审计绑定项（524 theorem/instance+2构造），audit PASS，facade49真实exit0。新增无噪声撑满条件 rank(M|kerB)=m>0 下的实际行Gram logdet绝对可积、期望高SNR偏移和0<=Delta<=m/(rho delta)；不是任意B/M的普遍偏移定理。三份最终源码Qoder P4真实返回，错误Gram/API/源维度警报已保留裁决。详见 WISHART_NOISELESS_LOGDET_OFFSET.md。首阶逆矩阵迹修正此时仍OPEN；冻结论文/完整构建/人工审查边界不变。本轮用户固定截止11:13:42UTC，自动任务保持PAUSED。

Latest2026-10-20 checkpoint515/auditPASS/facade48 realexit0: fixed arbitrary rectangular/singular/zero B:p-by-n and fixed M:m-by-n, actual complex rank(ZB+M)=min(m,rank stacked[B;M]) AE, equivalently min(m,rankB+rank(M restricted kerB)); actual expected full-logdet/logrho has that explicit limit. For n>0, COLUMN minimum atom at0 is1 iff this rank<n, else0. If M restricted kerB surjects onto m-dimensional output (m>0), fixed positive ROW minimum floor holds for EVERY noise, hence all nonnegative real ROW inverse minimum orders are integrable. No general singular inverse threshold/offset or growing-parameter uniformity asserted. 24 new declarations in8modules, not24 probability breakthroughs. All proof bodiesCodex;2realQoderP1+6final-sourceP4 delivered, errors/resolutions retained. Facade47 empty-log failure retained; same-gate unchanged-source retry48 actualexit0 withreceipt. WISHART_GENERIC_RANK.md / WISHART_NOISELESS_SPECTRAL_FLOOR.md exactscopes; WISHART_NEXT_NOISELESS_OFFSET_CARD.md remainsOPEN with scalar200000sample preflight only. HumanreviewREQUIRED/fullLakeNOT_RUN/frozenpublicationOLDUNCHANGED. Earlier latest/open-rank paragraphs below are historical and superseded only within this scope.

Latest2026-10-20 checkpoint491/facade45 actualexit0/auditPASS: actual arbitraryfixedB/M full-logdet expectedprelog=E rank(ZB+M), after deterministic spectral/rank bridge. No logL1/fullrank assumption. Deterministic genericrankformula min(m,rankB+rankMrestrictedkerB) STILL OPEN; finite64witnesscontrols only. WISHART_EXPECTED_RANK_PRELOG.md resolves falseP4fatal warnings against pinned exactdefinitions. No upstreamnoveltyclaim; humanreview/fullbuild/frozenpublication boundaries unchanged.

Latest2026-10-20 checkpoint488/facade44 actualexit0/auditPASS: expectedpositive-mode prelog for nonnegativeL1 spectra inclzeroatoms and actualarbitraryB/M; NO logL1/fullrank prerequisite. Generic rankformula stillOPEN/64exactfinitewitnesscontrols only. WISHART_ZERO_MODE_PRELOG.md/WISHART_NEXT_CORRELATED_RANK_CARD.md exactscopes. No mathematical/upstream novelty claim; humanreview/fullbuild/frozenpublication boundaries unchanged.

Latest2026-10-20 checkpoint483/facade43 actualexit0/auditPASS: actual arbitraryfactor full-logdet low-scale first/secondcoefficients CLOSED inclsingular/zeroB, plus expandedclosed S2. See WISHART_CORRELATED_LOGDET.md. Earlier undercheck wording below historical. General singular-factor highprelog rankformula stillOPEN; humanreview/fullbuild/frozenpublication unchanged.

Latest2026-10-20 checkpoint469/facade42 actualexit0/auditPASS: arbitraryfixed rectangular/singular B actual Gram-entry product, trace second/spectral second and centeredtracevariance CLOSED with trueL1. Exactclaims and P4 resolutions WISHART_CORRELATED_SECOND_MOMENTS.md. Earlier open correlatedmoment statements below historical. Correlated logdetlow-scale undercheck; notyetclaimed. FullbuildNOT_RUN/frozenpublicationOLDunchanged/[需人工审查].

# 金石等 (2008) Wishart 论文形式化：定理追踪表（B0）

Latest431/facade40: actual first and both distinct secondtrace moments/variance, explicit full-logdet first/second lowrho coefficients closed ALLiidshapes/fixedM. Arbitrary rectangular/singularfactor B actual Gram mean m B^HB+M^HM entrywise also closed (m-by-p source,p-by-n B); correlatedsecondmoments/curvature still controls-only. Exact claims/provenance table WISHART_LOGDET_RESEARCH_CLAIMS.md. Earlier checkpoint/openmean text below historical. Humanreview/frozenpublication/fullbuild boundaries unchanged.

Current420/facade38: ALL finite shapes/fixedcomplexM actual Etrace=mn+F and Etrace(Gram^2)=mn(m+n)+2(m+n)F+trace((M^HM)^2).re, F=SUM||Mij||^2. Full-logdet lowrho first/second coefficients now CLOSED, no rank/inverse-moment/density premise. Earlier unproved-mean/second-moment statements below are historical and superseded. Finalsource realQoderP4 delivered/resolved; humanreview/frozenpublication/fullbuild boundaries unchanged. See WISHART_GAUSSIAN_TRACE_MEAN.md and WISHART_NONCENTRAL_SECOND_MOMENT_CLOSED.md.

Latest386/facade32: actual Efull-logdet<=k log(1+rho*T/k), k=min(m,N)>0,T=actual finite expectedtrace,rho>=0. Low-scale Efull-logdet/rho->T at0right for all dimensions, no fullrank/inverse-moment assumption. Closed T=mN+normM_F^2 remains unproved here; no assumed tracevalue. See WISHART_LOGDET_MEAN_BOUND.md. Final3-source/two P4 responses retained/resolved, humanreview/frozenpublication/fullbuild boundaries unchanged.

Latest374/facade30: complete actual fixed-mean matrix logdet expectedprelog=min(m,N) for BOTH positive dimensions. Wide offset is Elogdet(XX^H), separately absolutely integrable; never use singular X^H X offset. Actual transpose Gaussian transport, no invented adjointlaw or spectraldensity. See WISHART_WIDE_LOGDET.md. Final2-source realP4 falsealarms/resolutions retained; first tooltag output not review. Humanreview/frozenpublication/fullbuild boundaries unchanged.

Latest365/facade29: actual SQUARE fixed-mean full-logdet offset Delta->0 butrho*Delta->realatTop(+infinity). Generic Fatou divergence and minimum-term lower bound proved; no divergent Bochner integral or exact log(rho)/rho coefficient asserted. Earlier statements saying square scaled divergence unproved are historical. See WISHART_SQUARE_LOGDET_ERROR.md. Final3-source P4 realresponse and resolutions retained, humanreview/frozenpublication/fullbuild boundaries unchanged.

Latest360 items/facade28: actual full-logdet offset error Delta>=0 bounded by rho^-p/p*SUM E(lambda_i^-p) for0<p<=1 andp<m-N+1. For STRICT m>N, rhoDelta->SUM E(1/lambda_i). Square allows fractional boundp<1 only; no finite square correction asserted. Individual inverse-p sufficiency from minimum criterion, not an individual IFF threshold. See WISHART_LOGDET_ERROR.md. Final3-source real P4 objections/resolutions retained, humanmodelreview REQUIRED. Fullbuild/frozenpublication unchanged.

Latest349 bounditems/facade27: actual full matrix logdet statistic log(Re det(I+rho X^H X)), arbitrary fixed mean, m>=N>0, has finite expected offset limit ElogdetGram after subtracting Nlogrho, hence prelog N. LogdetGram absolutely integrable including square case via inverse HALF moment. Not merely weakest-mode outage, but also not a communication mutual-information/coding derivation. Generic wrappers reuse mathlib Lp/DCT/spectral theorem; no upstream novelty claim. Final6-source P4 responses retained and specific warnings resolved; humanreview REQUIRED. See WISHART_LOGDET_EXPECTATION.md. Frozenpublication/full-build status unchanged.

Latest324 bound items/facade-26: for every CENTRAL (N+2)-by-N complex CN sample, N>0, actual CDF/x^3 ->N(N+1)(N+2)/36 and chosen density-core/x^2 ->N(N+1)(N+2)/12. Exact complement reindexing and low coefficients proved for all N, not interpolation. General-d simplified constant, noncentral sharp coefficient/G2 and full paper T1-4 correspondence remain open. See WISHART_TWO_SURPLUS_SHARP_CONSTANT.md. Prior numerical-only d2 statements below are historical, superseded by this result. Human review remains required; frozen manuscript and upload packages unchanged.

最新305项补充：中央任意形状实际最小值ONE维密度及其锐首项已闭合，源自已证CDF，
质量1/HasPDF/RN-pdf AE接口均证。非中心精确密度/联合G2与原一般T1-4对应不能由此
推定闭合；简化常数恒等仍开放。冻结稿件和投稿包没有自动更新。

2026-10-19硬边补充：中央任意m=N+d、N>0实际F(x)/x^(d+1)的严格正极限与有限
阶乘泛函系数和已证（291项/facade-23）。简化阶乘候选恒等和原一般T4常数对应尚未证；
一般非中心锐系数/G2仍开放。不要把已证分集阶数与原定理全归一化等同。

2026-10-19补充：一般固定均值、m>=N>0实际最小Gram特征值的逆矩对全部实p>0
可积iffp<m-N+1，临界及更高阶非负积分TOP；固定正vI和固定可逆复列因子ZB+M
同样成立。固定列相关的分集指数亦保持m-N+1。新增研究结论并非原一般T1候选
等式或一般非中心G2的完成；精确论文对应/人审仍开放。完整证据见271项研究审计。

建立：2026-09-27 后（S 会话）。**性质声明：本表由 S 依据仓库内已核验来源起草**
（`notes/jin_2006_wishart_summary.md`、`theory/jin_wishart_formalization/README.md`、
以及 S 实际读过的 Lean theorem 陈述）。B0 卡片原归 C 负责：**论文原文的逐条核对
（精确方程编号、参数域、记号约定）仍待 C 对照 arXiv:cs/0611007 PDF 完成**，
在此之前，所有依赖原文细节的单元格标 `[待核实]`，不得声称"逐条对齐"。

## 状态图例（按执行计划第 0 节的五个验收维度）

```text
陈述   = 论文定理的 Lean 陈述已固定（含假设与参数域）
基础设施 = 所需定义/测度/特殊函数已构建
模型→公式 = 从真实概率模型证到公式候选
公式→结论 = 公式候选等于论文结论（概率等式闭合）
审查   = 独立人工审查通过（测度论步骤）
```

| 维度取值 | `未陈述` / `仅公式侧` / `候选` / `已证` / `审查通过` |
|---|---|

## 当前状态（2026-10-19）

最新优先于下方历史范围：任意m>=N>0的实际中央最小CDF已由有限阶乘泛函固定
一元多项式给出，精确次数Nd、归一化和右尾首项已证。任意固定确定均值M的
非中心最小值则已证一般分集指数m-N+1，包含固定vI和高SNR阈值b/r；这是
T4的指数层进展，不是一般T4精确系数、非中心显式CDF或G2闭合。

| 最新实际范围 | 精确声明 | 限制 |
|---|---|---|
| 全矩形中央对数硬边指数 | `actualCentralRectangular_minimum_diversity` | m>=N>0，标量分支也由实际Gamma律证明 |
| 任意固定均值非中心对数硬边指数 | `actualNoncentralRectangular_minimum_diversity` | M固定，不允许误读为随SNR增长均值 |
| 固定M、固定vI、高SNR最小阈值 | `actualNoncentralCovarianceMinimumCDF_diversity` / `actualNoncentralCovarianceMinimumCDF_highSNR_diversity` | v>0，阈值b/r，b>0；指数不是精确前导系数 |
| 最弱模式自然对数outage推论 | `actualNoncentralMinimumModeOutage_diversity` | R>0；是log(1+r*lambda_min)，不是全MIMO logdet容量 |

研究证明说明见[WISHART_DIVERSITY_PROOF.md](WISHART_DIVERSITY_PROOF.md)，214项绑定
审计见verification/central_mixed_moments/audit.json。最终P4原回应与误报澄清均保留；
完整构建和独立人工语义验收未完成，冻结投稿稿件未同步。原T1一般候选恒等、
一般非中心G2、T3来源与一般T4精确系数仍开放。

新增一般中央实际结果：任意 t>=s 的闭式矩阵密度与归一化；任意 s>0 的中央 s×s 最小值 Exp(rate s)；标量协方差 vI 时 Exp(rate s/v)；整个正方矩阵在 W>xI 下减去 xI 的条件律。源码及核验映射见 [CENTRAL_WISHART_GENERAL_DENSITY.md](CENTRAL_WISHART_GENERAL_DENSITY.md)。这些不是一般非中心谱 G2，也没有完成原 T1 一般行列式候选的对齐。下面2026-10-15表保留为历史特例记录，不能据此把当前范围描述成仅2×2。原论文/投稿包未更新，[需人工审查]仍保留。

统一交接入口：[WISHART_STATUS.md](WISHART_STATUS.md)。原主表中的单列范围为历史基线；新增中央复2×2为已证多列特例，不能再统称“仅单列”。一般 (s,t,L) 的 T1–T4 仍开放。T3 源转录候选的严格局部反例与归一化来源疑点分开；不宣称刊版错误。完整构建未运行，最近主入口检查退出0。[需人工审查]不变。

| 新增实际范围 | 精确声明 | 验收 |
|---|---|---|
| 中央复2×2严格尾/完整CDF/实际指数律 | `JinWishart.actualTwoRow_minimum_tail` / `JinWishart.actualTwoRow_minimum_cdf_function` / `JinWishart.actualTwoRow_minimum_law_expTwo` | 叶子 PASS；CDF=1-exp(-2x)，尾=exp(-2x) |
| 原T1中央2×2候选→实际CDF | `JinWishart.theorem1CentralTwoRow_candidate_eq_actualCDF` | 五声明标准三公理；主入口 PASS |
| 实际标量协方差 vI | `JinWishart.actualTwoRow_scaled_minimum_law` / `actualTwoRow_covariance_minimum_CDF` | 十声明标准三公理；含本模块主入口 PASS |

## 2026-10-18 矩形中央新族

| 新增实际范围 | 精确声明 | 范围限制 |
|---|---|---|
| 任意 (n+1)×n 中央最小尾/完整 CDF/协方差 vI | `actualOneExtraRow_minimum_tail` / `actualOneExtraRow_minimum_cdf_function` / `actualOneExtraRow_covariance_minimum_CDF` | n>0，CN 总方差1；v>0 时 x/v；不是一般原 T1 候选 |
| 原 T1 中央三行两列候选→实际 CDF | `theorem1CentralTwoColumnThreeRows_candidate_eq_actualCDF` | 仅 (s,t,L)=(2,3,0)，原候选未改 |
| 多列中央 T4 最小硬边指数2 | `actualOneExtraRow_minimum_hardEdge` / `actualOneExtraRow_covariance_minimum_hardEdge` | 整个 t=s+1 族；系数 n(n+1)/4 或 n(n+1)/(4v²)，非一般 k/非中心 |

源码、失败记录、模型真实回应、控制和公理绑定见 `verification/rectangular_minimum/audit.json`。证明体 Codex；Qoder 路线/P4，Claude 限定 T1 P4；模型反馈不替代人审。以下主表为历史范围，不能把新的中央多列族描述成未证。

## 2026-10-19 实际矩与第二矩形族

任意两个主子式的真实联合整数矩（显式交集/差集基数依赖）已证，嵌套和不相交均为特例。任意(n+2)×n中央最小值已证有限多项式严格尾、完整CDF和标量协方差vI替换x/v；与上一轮(n+1)×n族区别开。当前52公开声明含1有限构造的核验绑定见verification/central_mixed_moments/audit.json，主入口通过、未完整构建；新有限矩P4超时、d=2概率P4限定交付，人审未完成。没有证明原一般T1行列式候选相等，也未扩称非中心G2或一般d>2闭合。详见CENTRAL_WISHART_GENERAL_DENSITY.md，冻结稿件/投稿包未同步。

## 主表

**2026-10-09 用户提供 AI4M 指南后的更新：** 实际 LeanSearch 检索并复用
`Finset.powersetCard_one` 后，`T3CentralNormalizationClosure` 已证通用候选等于
显式两项，所以具体 `(s,t,L,k,x)=(2,3,0,2,2)` 转录候选不等于任何事件概率，
并在真实中央 `3×2` Gaussian 谱事件上编译回归。历史“三次未闭合”记录保留，
但 API 缺口现已关闭。不是完整 T3 概率公式，刊版和边界解释仍 [需人工审查]。
详见 `AI4M_GUIDE_TOOL_USE_20261009.md`。

**2026-10-09 T3 源对齐修复：** 原表先前称 `c₃` 已按分母编码，但实际
`theorem3C3` 仍是乘法，现已修正；`T3ScalarNormalizationBridge` 证明其与独立
审计的显示常数一致。列因子推导的额外 `Γ_(s-L)(t-L)` 仍单独保留，中央
`s=2,t=3` 数值控制提示显示式可能缺项，正式版本/勘误尚待核对。
这关闭本地标量转录错误，不关闭 T3 实际概率公式。见
`T3_SCALAR_SOURCE_ALIGNMENT_20261009.md`（构建、公理和数值验证均通过）。

**T3 严格局部见证：** `T3CentralNormalizationWitness` 已证 `s=2,t=3,L=0,k=2,x=2`
的两个显式混合行列式之和实部严格大于 1。通用 powerset 和到两项的 API 桥三次
未闭合后停止，未声称 `theorem3IncrementCandidate` 整体已判假；源版本解释与刊版
复核仍 [需人工审查]。见 `T3_EXPLICIT_NORMALIZATION_WITNESS_20261009.md`。

| 论文条目 | 原文假设/参数域 | 概率模型 | 原结论 | 对应 Lean（文件 : theorem） | 状态 | 缺口与证据 |
|---|---|---|---|---|---|---|
| **Theorem 1** 最小特征值 CDF（Nuttall Q + 上不完全 Gamma 的行列式比值） | `s=min(n,m)`, `t=max(n,m)`, `L≥0` 秩非中心，空间白化复高斯，完美 CSI `[待核实：精确方程编号]` | 非中心复 Wishart 有序特征值 `φ₁>…>φₛ>0` | `P(φₛ≤x)` = 行列式比值 | 公式侧：`Theorem1Formula.lean : theorem1CdfCandidate`；中心单列任意行：`WishartGamma.lean`；非中心 `1×1`：`ScalarNoncentralTheorem1.lean`；**`2×1` 任意非零复均值：`Theorem1TwoRowsActualCDF.lean : theorem1TwoRowsCandidate_eq_actualCDF`**（+ 中心分支）；**`3×1` 单列非中心任意均值方向：`Theorem1ThreeRowsActualCDF.lean : theorem1ThreeRowsOneColumnCandidate_eq_actualCDF`**（`λ>0,x≥0,‖encodedMean‖²=2λ`）；直接 Frobenius 参数推论：`Theorem12ThreeRowsFrobeniusCDF.lean : theorem1ThreeRowsOneColumnCandidate_eq_actualCDF_frobenius`；单列任意行仅公式侧：`Theorem1SingleColumnAnyRows.lean` | 陈述✅ 基础设施✅ 模型→公式：`2×1` 任意均值✅ / `3×1` 任意均值方向✅ / 一般❌；公式→结论同范围；审查❌ | 一般 `(s,t,L)` 未证；分母非零覆盖已闭合的 `1×1`、`2×1` 与此 `3×1` 单列特例；`2×1`、`3×1` 的换元/球面积分/Fubini 标 `[需人工审查]`；论文竖线=行列式 vs Lean 候选对复行列式取模长，等价性未证 `[待核实]` |
| **Theorem 2** 最大特征值 CDF（Nuttall Q 差 + 下不完全 Gamma 的行列式比值） | 同上 | 同上，`φ₁` | `P(φ₁≤x)` = 行列式比值 | 公式侧：`Theorem1Formula.lean : theorem2CdfCandidate`（含 `Ξ(x)+Ψ(x)=Ψ(0)` 逐元素关系）；中心单列：`WishartGamma.lean`；非中心 `1×1`：`Theorem2NoncentralScalarFormula.lean`；**`2×1`：`Theorem1TwoRowsActualCDF.lean : theorem2TwoRowsCandidate_eq_actualCDF`**（+ 中心分支）；**`3×1` 单列非中心任意均值方向：`Theorem2ThreeRowsActualCDF.lean : theorem2ThreeRowsOneColumnCandidate_eq_actualCDF`**（`λ>0,x≥0,‖encodedMean‖²=2λ`）；直接 Frobenius 参数推论：`Theorem12ThreeRowsFrobeniusCDF.lean : theorem2ThreeRowsOneColumnCandidate_eq_actualCDF_frobenius`；单列任意行仅公式侧：`Theorem2SingleColumnAnyRows.lean` | 陈述✅ 基础设施✅ 模型→公式：`2×1` 任意均值✅ / `3×1` 任意均值方向✅ / 一般❌；公式→结论同范围；审查❌ | 仅已闭合的单列与 `3×1` 单列特例；多列和一般 `(s,t,L)` 仍未证；Theorem 1 同类换元/Fubini 标 `[需人工审查]`；原文行列式模长记号仍 `[待核实]` |
| **Theorem 3** 第 `k` 个特征值 CDF 递推 | `2≤k≤s`, `x>0`；`λ₁>⋯>λ_L>0` 为非中心矩阵正互异非零特征值（(25) 有 Vandermonde 分母） | `S∼W_s(t,I_s,Ω)`，有序特征值 `φ₁>⋯>φ_s>0` | (23) `F_{φ_k}(x)=F_{φ_{k−1}}(x)+p`；`p` 是 `φ_s<⋯<x<φ_{k−1}<⋯<φ₁` 的概率。 (24) `p=c₃Σ₁detΘ(x)`，系数及分块行矩阵由 (25)–(26) 给出（arXiv:cs/0611007v2，印刷页 7） | `PaperStatements.lean : orderedEigenvalueLaw_kthCDFRecurrence_strict`（抽象 1-based 第 `k` 大事件递推，假设阈值无原子）；**真实模型无条件版：`ThresholdNoAtom.lean : paperModel_kthCDFRecurrence_strict`**；`T3FixedCardinalityRowSelection.lean : coeff_det_rowAffinePolynomial_eq_fixedCardRowSum`；`T3PaperThetaSpecialization.lean : theorem3ThetaDetSum_eq_polynomialCoefficient`（Ψ、Ξ、Θ 及已修正为分母 `Γ_{s-L}(s-L)` 的 `c₃` 代数编码）；退化单列见 `OneColumnCDFRecurrence.lean` | 陈述🔶（(23) 抽象事件递推✅，(24)–(26) 代数表达式✅）基础设施✅ 模型→公式❌ 公式→结论❌ 审查❌ | 论文 Θ 行混合和已证明等于 `det(Ξ+XΨ)` 指定系数；尚未证明 `c₃ΣdetΘ` 等于概率 `p`。特别 `c₁→c₃` 的列归一化发现了未解释的 factorial 因子，正在对抗审计；联合谱密度 (52)–(55)、Appendix C 有序域拆分/Fubini 也未形式化。真实谱简根/阈值无原子仍未连接此模型。重复 `λ` 时 (25) 分母为零，已显式限制正互异谱输入 |
| **Theorem 4** 小阈值渐近（密度最低次幂 `dₖ=(s-k+1)(t-k+1)-1`，CDF 最低次幂 `(s-k+1)(t-k+1)`） | 小 `x` / 高 SNR 主导项；新单列结论 `s=k=1,t=m>0`，单位复方差，任意复均值 | 实际 Gaussian Gram 推前律 | CDF 首项 + 分集阶数 | **任意行数、任意复均值单列：`T4NoncentralOneColumnAnyRows.lean : noncentralOneColumnSmallestCDF_div_tendsto_frobenius`**，`F_M(x)/x^m→exp(-∑‖Mᵢ₀‖²)/m!`，包括零均值；中心基础：`T4CentralOneColumnAnyRows.lean`；旧非中心两行：`TwoRowSmallOutageAsymptotic.lean` | CDF 实际模型单列任意 `t`✅；密度渐近/多列❌；审查❌ | 新证明不假设候选谱密度，不含待证归一化前提；一般 `s>1` 的谱相互作用、密度渐近和通用 SER 仍未做。[需人工审查] 方差、平移、积分及参数映射；详情 `T4_NONCENTRAL_ONE_COLUMN_ANY_ROWS.md` |
| 推论：Rice 因子单调性（式 (45)） | `K>0`, `n=st` | 确定性 | `(K+1)^n exp(-Kn)` 在 `K>0` 严格递减 | `JinWishartFormalization.lean : riceFactor_strictAntiOn`（+ 导数负） | 陈述✅ 基础设施✅ 模型→公式✅ 公式→结论✅ 审查✅（确定性论证，无测度论） | 无 |
| 推论：分集阶数 / 最弱模最小 SNR | 等功率、非负缩放 | 确定性 | 分集阶数 `(s-k+1)(t-k+1)`；最弱模 SNR 最小 | `PaperStatements.lean : DiversityOrderClaim`（算术✅）；`JinWishartFormalization.lean : weakest_mode_has_smallest_snr` | 陈述✅ 基础设施✅ 模型→公式✅ 公式→结论✅ 审查✅ | 概率侧（ outage=第 r 模 CDF ）见下一行 |
| 推论：等功率 outage / SER | 等功率、`r` 个模、完美 CSI | 多列 Wishart 最小特征模 | outage = 第 `r` 特征值 CDF；平均 SER 核 | `MIMOPerformance.lean`（弱/严格事件换算✅，零原子引理✅）；`MIMOWishartSER.lean`（平均 Q 减量 = CDF 补函数加权积分✅）；**论文式 (42)–(44) 的 `2×1,s=1,t=2,r=1` 物理 outage 特例：`PaperSingleStreamTwoRowOutage.lean`**；无原子性：单列✅（`OneColumnNoAtom.lean`）/ 多列❌ | 陈述✅ 基础设施🔶 模型→公式：抽象核✅ / 论文 `2×1` outage✅ / 一般❌ 公式→结论🔶 审查❌ | `2×1` 已闭合物理缩放、Rice 参数及高 SNR 系数；多列最小特征值无原子性未证，通用 SER/多流 outage 与论文一般参数域仍未闭合 |

## Python 侧（infoq）能力边界 —— R1 同步（S 负责，2026-09-27 后核验）

```text
[infoq 能力边界]
- infoq.check 四态：PROVED（精确有理证书，在所给约束下的无条件证明）/
  NOT_IDENTIFIED（已证不在 Shannon 锥内，≠命题为假；Ingleton、Zhang-Yeung 1998
  属预期此类）/ UNVERIFIED（LP 数值可行但证书复核失败，只是数值证据）/
  SOLVER_ERROR（求解器未正常结束）。
- 约束：马尔可夫链 "X-Y-Z"（自动展开成对条件独立）；一般等式 "I(X;Z|Y) = 0"。
- 语法：H(X,Y)、H(X|Y,Z)、I(X;Y)、I(X1,X2;Y|Z)；标量倍乘 *（可省略）、
  分数系数；禁止信息量相乘与非零常数项。
- 数值预言机 infoq.Oracle：随机采样 + Nelder-Mead 精修；输出 gap /
  counterexample / tight。纪律：反例=构造性否定；紧性=路线提示；
  都不是证明；紧而不等的假命题数值上可能漏检。
- 测试：tests/ 五文件，静态 101 个用例（协调者实跑数以 unittest 输出为准）。
- 边界：Shannon 锥只覆盖元素不等式组合；非 Shannon 型命题、测度论步骤、
  极限交换超出 LP 能力，必须人工/其他工具。数值证据永不冒充证明。
```

## 未闭合缺口清单（按优先级）

1. **G1 ✅（谱可测范围）** 论文小侧 `s×s` Gram 的有序特征值向量可测性现已闭合：实对称有限维 Courant–Fischer min-max
   已在 `IndexedCourantFischerProof.lean` 证明；复 Hermitian/RCLike Weyl 扰动界在
   `WeylComplexHermitian.lean : abs_eigenvalue_sub_le_operatorNorm_rclike`；同文件的
   `orderedHermitianEigenvalueCoordinatesContinuous` 证明 Hermitian 有序特征值坐标 Lipschitz
   连续；`PaperSmallSideGram.lean` 定义 `Fin (min m n)` 上的实际小侧 Gram，证明 shifted
   Gaussian 样本到 PSD 矩阵的可测性；主 facade 的
   `measurable_paperSmallSideSampleEigenvalueVector` 再组合谱坐标连续性，直接给出论文小侧
   整组有序谱的可测性。旧 `measurable_complexNoncentralSampleEigenvalueVector` 仍表示
   `XᴴX` 的 `n` 维谱；两种 Gram 非零特征值多重集对应关系尚未证，但不影响小侧随机矩阵的
   直接定义/可测性。此卡仅关闭确定性模型→随机变量的谱可测桥，不包括重根零测、联合密度或
   论文 CDF 闭式。
2. **G2** 非中心 Wishart 全部有序特征值联合密度及测度变换（奇异值分解/Jacobian、酉群
   积分、重根零测）仍未闭合。`RepeatedRootNullSets.lean` 证明一元实多项式零点集
   零测及绝对连续测度推论；`MvPolynomialZeroSetNull.lean : mvPolynomial_zeroSet_volume_eq_zero`
   证明任意有限维实非零多项式零点集零测；**`WishartSimpleSpectrum.lean`（S，2026-09-27
   晚新增并接入 facade）把重根零测推广到任意维度 d 的实矩阵：特征多项式有重实根的
   d×d 实矩阵集合 Lebesgue 零测。技术路线是 resultant（`resultant_map_map` 函子性）
   + 对角见证矩阵的可分性（`separable_prod_X_sub_C_iff`），绕开了 mathlib 判别式引理
   只覆盖 2/3 次的缺口；它推广了 `MvPolynomialGramTwoByTwo.lean` 的 2×2 原型。**
   **复 Hermitian 情形已闭合（2026-09-28，`ComplexGramSimpleSpectrum.lean`，已接入 facade）：**
   在 `2mn` 个实坐标的复系数多项式环上构造通用样本矩阵及其 Gram，取特征多项式与导数的
   resultant；证明复系数非零多元多项式的实零点集零测（`complexMvPolynomial_realZeroSet_volume_eq_zero`），
   用对角见证均值证明 resultant 非零，再经平移与 Gaussian 绝对连续得到
   `paperSmallSideGram_eigenvalues_strictAnti_ae`：**任意 `m×n`、任意确定性复均值 `M`，论文小侧
   `s=min(m,n)` Gram 的有序特征值几乎必然严格递减 `φ₁>⋯>φ_s`**（另有 `XᴴX`、`n≤m` 版本
   `complexSample_shiftedGram_eigenvalues_injective_ae`）。`#print axioms` 仅 propext/Classical.choice/Quot.sound。
   这闭合了 Theorem 3 递推的阈值严格/弱事件替换所需"谱简根"前提的随机矩阵侧；**阈值无原子
   已闭合（2026-09-28，`ThresholdNoAtom.lean`）**：`paperModelEigenvalue_atom_eq_zero` 证明任意固定
   `x` 下每个有序特征值无原子；`paperModelLaw` 把真实模型实例化为 `Paper.OrderedEigenvalueLaw`；
   `paperModel_kthCDFRecurrence_strict` 使论文式 (22) 在真实模型上无条件成立。
   **2026-10-09 Gaussian 原始样本桥：** `GaussianMatrixSpectralIntegral.lean` 证明任意
   `m,n,M` 下实际非中心整谱 law 为已证移位 Gaussian 密度的推前，Borel 谱事件
   为原始实编码样本空间的密度积分；没有候选 `hDensity` 前提。具体跨阈值事件、
   总质量与公理检查见 `GAUSSIAN_MATRIX_SPECTRAL_INTEGRAL_20261009.md`。
   **2026-10-09 原始复坐标缩放桥：** `GaussianRawCoordinates.lean` 将实际任意
   矩形样本律在原始实部/虚部 Euclidean 坐标中证明为
   `pi^(-mn) exp(-||X-M||_F^2)` 密度，核对条目、均值、Frobenius 能量，
   并给出实际整谱事件的原始坐标积分。它复用锁定 mathlib 的 Haar 缩放定理；
   这是样本空间密度，不是 Gram/联合谱密度，测度及模型对应仍 `[需人工审查]`。
   **2026-10-09 两列外层/内层积分：** `GaussianTwoColumnIntegration.lean`
   证明实际任意 `m×2` 样本的列乘积律、非负 Tonelli、任意均值下真实谱事件的
   两列迭代积分，并用现成 `skew_product` 证明可测首列依赖的第二列实等距变换
   保持 Gaussian 乘积律。它尚未构造保复 Gram 的具体酉 QR 框架或 Bartlett 律。
   `GaussianComplexColumnFrame.lean` 进一步复用现成实/复正交基，核对编码坐标
   与实际方差；证明真正复酉框架在编码列上的 Gaussian 不变性，以及两实际列
   同时变换后完整 Gram 不变，连接可测首列依赖复酉框架的第二列乘积律。
   尚未提供对齐首列的具体 QR 框架或残余能量/联合 Gram 密度。
   `GaussianComplexInnerProductLaw.lean` 用既有特征函数/唯一性定理识别固定首列后
   实际任意 `m×2` Gram 非对角项的完整复 Gaussian 推前律，包含零列边界和
   `sqrt(2)` 方差尺度。验收及剩余缺口见同日同名笔记；它不单独证明联合 Gram 密度。
   **2026-10-10 残差独立卡：** `GaussianComplexOrthogonalResidual.lean` 对任意行数、
   固定单位复方向证明投影与整个正交残差（以及其能量）独立，实际方差列的
   投影/残差联合律等于乘积律，并给出精确能量分解。复用既有联合 Gaussian
   不相关推出独立定理，非从头构建独立性库。验收记录见
   `GAUSSIAN_COMPLEX_ORTHOGONAL_RESIDUAL_20261010.md`；仍缺随机首列及残差 Gamma/
   Gram 联合密度桥，不宣称固定投影结论自动等于随机 QR 分解。
   `ComplexTwoRowResidualEnergy.lean` 进一步将二维复残差能量识别为实际 Exp(1)
   推前，并得到固定单位方向的投影/残差能量联合律 Gaussian × Exp(1)。
   复用既有 CDF 唯一性和径向律，不重复径向积分。详见
   `COMPLEX_TWO_ROW_RESIDUAL_ENERGY_20261010.md`；随机首列与 Gram/谱密度仍缺。
   **随机方向/Bartlett 桥：** `TwoRowRandomDirectionLaw.lean` 在中心 `2×2` 实际样本上，
   构造可测且处处单位的首列方向（含零回退），复用 skew_product 提升固定纤维律，
   证明实际 `(首列能量,投影,残差能量)` law 为 Gamma(2,1) × CN(0,1) × Exp(1)，
   实际完整 Gram law 等于其明确矩阵映射的推前。详见
   `TWO_ROW_RANDOM_DIRECTION_LAW_20261010.md`；这不含 Gram/谱 Jacobian 或非中心核。
   `TwoRowGramChart.lean` 补上正首能量 S>0 的四实 Gram 图，核对既有实际 Bartlett
   映射，证明左逆/注入、实际 Fréchet 导数、Jacobian=S 和具体非负 Lebesgue 换元。
   记录 `TWO_ROW_GRAM_CHART_20261010.md`；联合坐标密度/volume 对齐、边界支持及
   谱 Jacobian/角积分仍未闭合，不能仅凭坐标换元宣称实际 Gram/谱密度已证。
   **2026-10-10 本地模型交接：** `TwoRowGramSupport.lean` 进一步验收正首能量、
   正残差域的准确 Gram 坐标图像、右逆与行列式=S×E。这四条由 Codex 补充；
   DeepSeek 本地九次生成均未通过验收，不能列为本地模型已证成果。
   主构建、公理及边界回归通过，详见 `DEEPSEEK_WISHART_PROGRESS_20261010.md`。
   本卡只关闭确定性支持域代数，不关闭几乎必然支持/边界零质量或实际密度。
   尚未闭合：Gram/谱 Jacobian、角积分及
   联合谱密度。这仍是 Theorem 1–3 一般维度模型等式前置的大缺口。
3. **G3** 一般维度 Theorem 1–3 的概率等式：仅公式侧约化（单列任意行）。
4. **G4** 一般 Theorem 4 / SER / outage 封闭：`T4DensityToCDF.lean : density_to_cdf_hardEdge`
   已抽象证明若密度为 `u^d g(u)` 且 `g(u)→a`，则 CDF 积分首项系数为 `a/(d+1)`；中心单列任意行数、
   `SixDimensionalAngularBesselI2.lean` 证明 S⁵ 轴向核的 I₂ 级数积分，`SphereSixDAxialMeasure.lean`
   又证明 `toSphere` 测度上的指数核角图公式；`NoncentralSixDimensionalRadial.lean` 把轴向六维高斯
   球壳核等同于 Nuttall `(3,2)` 被积核除以振幅平方，且已证核非负、可测与中心参数总质量 `1`；
   `ThreeRowSampleCoordinates.lean` 已证明对任意复 `3×1` 均值，真实最小 Gram 特征值弱 CDF
   等于以均值实振幅为参数的有限半径径向级数积分；
   **2026-10-09：任意正行数非中心单列的实际 CDF 首项已证**（`T4NoncentralOneColumnAnyRows.lean`），包括零均值。一般 Wishart 多列非中心密度的首项展开/系数、
   可积性及极限交换尚未给出，因此一般 Theorem 4 与通用 SER/outage 仍未完成。
5. **人工测度审查**：`2×1` 闭环（M2/M3/M4）的全部 Fubini/换元/参数对应项。
6. **记号核对** `[待核实]`：论文行列式记号 vs Lean 复行列式取模长；论文
   `Ω`/散射尺度 `ε` 与 Lean 单位方差约定的参数映射。

## 维护规则

- 每张任务卡（B0/P1/P2/L*/M*/G*/R1）完成时更新对应行；只用经构建证明的事实，
  公式侧、候选密度、真实概率律、论文定理四级分开记录。
- 本表由 C 拥有最终核验权；S 只同步 Python 侧与只读复查结论。
- 引用不确定一律 `[待核实]`；不得以"基本完成"等模糊措辞关闭任何行。

2026-10-10协作验收补记：TwoRowBartlettSupport六条关闭实际中心2x2 Bartlett能量严格正性的几乎必然支持/非正边界零质量。复用本地Gamma零单点引理，仍不是Gram或谱密度。新协作窗口本地54次生成仅2条候选复密度函数辅助（非负、可测）通过；实际复Gaussian密度等式与联合密度未闭合。详见DEEPSEEK_CODEX_COLLABORATION_HOUR_20261010.md。

2026-10-10用户继续后的Codex修复：TwoRowGramPositive四条关闭实际中心复Gaussian2x2 Gram行列式=S*E、行列式实部几乎必然严格正、行列式零事件零测，复用此前实际Bartlett正性。仅标准三公理。该结果没有Gram/谱密度结论，一般论文定理仍开放，测度与模型对应[需人工审查]。
