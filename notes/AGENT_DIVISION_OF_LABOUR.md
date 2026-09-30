# 双 Agent 分工与交接（StepCode 会话 ↔ Codex 会话）

更新：2026-09-27 之后第二轮（S 只读核验轮，本机 shell 恢复可用，**实跑了
测试与构建**）+ **第三轮分工提案（第 10 节，S 起草，待 C 与协调者确认）**。
快照基准：`git HEAD = 5e48071e`（提交于 2026-09-27），此后工作区又有大量
未提交改动（C 持续推进 Lean 侧）。本文件是**两个 AI 执行者之间的协作契约**，
不是给用户看的进度报告。
上游规范见 `notes/JIN_WISHART_EXECUTION_PLAN.md`（由 Codex 会话编写），本文件只记录
"谁拥有哪些文件、各自进展到哪、下一步该谁动"。

## 0. 为什么需要这份文件

用户同时在运行两个 agent 会话，都工作在 `D:\vibe math`：

| 会话 | 身份 | 擅长 |
|---|---|---|
| **S** | StepCode / Claude（本文件作者） | Python 工具链、测试、LP 语义、只读侦察 |
| **C** | Codex | Lean 4 证明、测度论、`apply_patch` 流程 |

两者共享同一工作区和同一把 API key。**没有直接的消息通道**——协作完全通过
(a) `AGENTS.md`、(b) `notes/JIN_WISHART_EXECUTION_PLAN.md`、(c) 本文件、
(d) git 提交历史 这四份共享文本完成。任何一方动手前先读这四份。

## 1. 文件所有权（硬边界，越界即冲突）

| 文件 / 目录 | 所有者 | 状态 |
|---|---|---|
| `infoq/expr.py` | **S** | 已改完（乘法/除法解析），本轮只读复核通过 |
| `infoq/shannon_lp.py` | **S** | 已改完（四态状态机），本轮只读复核通过（仅补两处文档：模块 docstring 四态说明、`ShannonResult.status` 过时注释） |
| `infoq/converse.py`、`infoq/__init__.py` | **S** | 已同步新状态，本轮只读复核通过 |
| `tests/`（全部） | **S** | 用例全绿（第二轮实测 105 个 OK）；`tests/README.md` 的 P2 说明**已就位**；仍未纳入版本管理 |
| ⭐ `experiments/`（既有 `blahut_arimoto.py` 之外的新文件）、`verification/` | **S** | **第 10 节分工提案新增项，待协调者批准后生效**；本轮 S 已在 `experiments/` 建 2 个只读工具/数值脚本 |
| `theory/jin_wishart_formalization/**` | **C 停工后转交 S**（2026-09-27 20:00 协调者指派；C 于 19:43 停止写入，最后动作是修好 `MvPolynomialZeroSetNull.lean`） | L1/L2/L3 已完成；M1–M4 的 `2×1` 闭环完成到"任意复均值"（见第 2 节）；G1 已闭合，G2–G4 进行中 |
| `notes/JIN_WISHART_EXECUTION_PLAN.md` | **C**（停工；S 只读，不追加） | C 的规范文件（含 2026-09-27 执行状态补记）。C 停产后 S 的 Lean 进展记入本文件，不写进计划书 |
| `notes/AGENT_DIVISION_OF_LABOUR.md` | **S** | 本文件 |
| `.workbuddy/`、`.write_probe.tmp` | 未定 | 双方都不删、不提交，等用户裁决 |
| `README.md`、`AGENTS.md` | 协调者（用户） | 需双方成果汇总后由用户/协调者改。**注意：根 README 的 infoq 速查仍只写两态，未反映 P2 四态** |

## 2. 任务卡台账（对齐 C 的计划编号）

| 卡 | 内容 | 负责 | 状态 |
|---|---|---|---|
| B0 | 基线与定理对照表 | C | 🔶 **S 已起草** `notes/JIN_WISHART_THEOREM_TRACKER.md`（依据仓库内已核验来源，未读论文 PDF）：定理 1–4 + 三条推论逐行列明五维状态；**论文原文逐条核对仍待 C**（精确方程编号/参数域/记号，表中已标 `[待核实]`） |
| **P1** | 审查表达式解析器补丁 + 测试 | **S** | ✅ **S 已完成**；C 未留书面审查意见，本轮 S 只读复核通过 |
| **P2** | LP "无精确证书却 PROVED" | **S** | ✅ **S 已完成**；同上 |
| L1 | `NuttallQ21Normalization` 修复 | C | ✅ C 已完成，且已并入主入口 |
| L2 | `ScalarPhysicalScaling` 修复 | C | ✅ C 已完成，且已并入主入口 |
| L3 | 四个游离模块并入主入口 | C | ✅ **已完成**（facade 已 import 全部四个；此后 C 又新增 29 个未提交模块，其中 3 个未并网，见 8.5 节） |
| M1 | 球面推前分布精确陈述 | C | ✅ 基本完成（`SphereFourDPlanePolar` / `SphereFourDPlaneAngleChart` / `FourDimensionalPolarBridge` / `NoncentralFourDimensionalSphere`） |
| M2 | 从真实高斯律到径向密度 | C | ✅ 已完成（`NoncentralFourDimensionalCDF` / `NoncentralFourDimensionalGaussianCDF` / `TwoRowSampleCoordinates`） |
| M3 | 特殊函数正规化和边界 | C | ✅ 已完成（`NuttallQ21Normalization` 桥接 `nuttallQ 2 1 a 0 = a`） |
| M4 | 论文 `2×1` 定理 1/2 对应与审稿 | C | 🔶 陈述+证明已由 `Theorem1TwoRowsActualCDF.lean` 完成到**任意非零复均值**（Theorem 1 与 2 的 `(1,2,1)` 候选式 = 真实 CDF）；**人工测度审查仍未做** |
| G1 → G4 | 一般维度长线 | C | G1 ✅ 已闭合（`IndexedCourantFischerProof` 证实对称 Courant–Fischer min-max；`WeylComplexHermitian` 证 Hermitian Weyl 界与有序谱连续；`PaperSmallSideGram` 建小侧 Gram 可测；台账缺口清单第 1 条已关闭）。G2–G4 未开始（`TwoRowSmallOutageAsymptotic.lean` 的 T4 `2×1` 渐近已是 public theorem，`T3FixedCardinalityRowSelection`/`T4DensityToCDF` 是 G3/G4 的泛型砖） |
| R1 | 台账 / 文档 / 独立审查 | 双方 | 持续。本轮 S 完成一次独立只读复查（见第 8 节） |

**并行规则**（沿用 C 的计划第 3 节）：P1/P2/L1/L2 可由不同执行者在不同文件上并行；
M1 之后的测度论证明**必须串行**，因为结论高度依赖前一环节的精确定义——S 不介入。

## 3. S 的交付详情

### P1 — 表达式解析器（`infoq/expr.py`）

**问题**：词法分析器把 `*` 和 `/` 收进了 symbol 表，但递归下降 parser 从未处理它们，
导致 README/AGENTS.md 承诺的语法全部抛 `ExprError`：

```
"2*I(X;Y)"        → ExprError 非零常数项 2 无意义
"3/2*H(X,Y,Z)"    → ExprError
"2*(H(X)+H(Y))"   → ExprError
```

**修法**：把 `_parse_term` 重写成真正的乘法层。语义约束——`*` **只表示标量倍乘**，
信息量之间相乘仍被拒绝（那不再是信息量的线性组合）。

已验证：

- 19 种合法写法全部解析正确，含 `2*I(X;Y)`、`3/2*H(...)`、`2*(...)`、`(1/3)*H(X)`、
  隐式乘法 `2 I(X;Y)`、反向 `I(X;Y)*2`、链式 `2*3*I(X;Y)`、`2 / 3 * I(X;Y)`
- 12 种非法写法全部抛 `ExprError`（而非别的异常或静默通过），含 `H(X)*H(Y)`、
  非零常数项、尾随/连续 `*`、`1/0`、保留字作变量名
- **解锁的新能力**：带分数系数的命题现在能判定。Zhang-Yeung 1998
  （`2*I(X3;X4) <= ...`）此前根本输不进去，现在正确返回 `NOT_IDENTIFIED`
- 四个 demo 脚本（`verification/` ×3 + `experiments/blahut_arimoto.py`）全部仍通过

### P2 — LP 四态状态机（`infoq/shannon_lp.py`）

**问题**：`check()` 在 LP 数值可行、但证书有理化/精确复核失败时，仍返回 `PROVED`
并带空证书。这与 AGENTS.md 铁律 2/3（"证书已用精确有理数复核，这是真正的证明"）冲突。

**修法**：引入四态，语义严格分离。

| 状态 | 含义 |
|---|---|
| `PROVED` | 有精确有理证书、元素不等式组合系数非负、向量恒等式精确成立 |
| `NOT_IDENTIFIED` | LP 已证明不在 Shannon 锥内（**不代表命题为假**） |
| `UNVERIFIED` | LP 数值可行但证书未过精确复核 —— **只是数值证据，不是证明** |
| `SOLVER_ERROR` | 求解器未正常结束（迭代上限/无界/数值错误） |

同时：

- 显式检查元素不等式组合系数非负（`alpha` 来自 `(0, None)` 边界，数值上可能出现
  极小负值；有理化后仍为负即判失败）
- 等式命题：任一方向未核实，整体不得判 `PROVED`
- **移除了从未使用的 `tol` 关键字参数**。它是个陷阱：看起来能调证明等级，实际什么都没做
- `converse.format_report` 现在按状态分别计数，区分"不在锥内"与"未能核实"

**测试**：用 `unittest.mock.patch` 定向触发罕见分支，不靠随机 LP 碰运气。
共 23 个新用例，覆盖：有理化失败降级、空证书合法、求解器三种异常码、
负系数拒绝、等式状态传播、报告区分、`tol` 已移除。

## 4. S 对 C 的一处纠正的接受

C 在计划书第 1 节纠正了 S 的早期判断：

> "`I(X;Y)=I(Y;X)` 一类零目标的**空证书可以有效**，不能用'证书列表为空'
> 证明 LP 有 bug。真正的 bug 是证书生成失败时返回 `(None, None)`，而上层仍把
> 状态设为 `PROVED`。必须区分 `None` 和 `[]`。"

**S 接受这个纠正。** S 此前的表述"实测触发过空证书路径（`I(X;Y) = I(Y;X)` 返回
cert items: 0）"是**误导性的**——那个案例是目标恒为零时的合法空证书，属于成功路径，
与失败路径无关。真正的缺陷确实只是"失败时仍返回 `PROVED`"。

这个区分现在已经固化为测试：

- `TestEmptyCertificateIsValid.test_zero_target_empty_certificate_is_proved`
  —— 空证书必须仍判 `PROVED`
- `TestEmptyCertificateIsValid.test_empty_certificate_not_mistaken_for_failure`
  —— 同一 `PROVED` 下，合法空证书与失败路径的 message 必须不同
- `TestUnverifiedBranch.*` —— 失败必须降级为 `UNVERIFIED`

## 5. 待办与阻碍

**给 C**：

1. 审查 P1/P2 的 diff（`git diff -- infoq/`）。P2 改了公开 API：移除 `tol` 参数、
   新增 `UNVERIFIED` / `SOLVER_ERROR` 两个导出。若有调用方依赖需说明。
2. L3：`NuttallQ21Normalization` 现已单独构建通过。C 计划里提到要"另立桥接引理，
   证明实积分表达式确实等于 `nuttallQ 2 1 a 0 = a`"——这一步是 M3 的前置，S 不介入。
3. `OrderedEigenvalueMeasurable` 目前只覆盖最大/最小特征值可测性，**不等于**内部
   有序特征值全部可测（C 已在计划里标出，此处重申以免被遗忘）。

**给 S（下一轮，需用户指派）**：

1. P1/P2 若被 C 审查后有修改意见，按意见改并补测试。—— **本轮已查：C 未留下任何书面审查意见**（notes/ 与 theory/ 全文检索无 infoq 相关反馈），维持原状。
2. `tests/README.md` 需补 P2 的说明。—— **本轮已核实：已就位**（`test_shannon_lp_status.py` 一行 + 设计原则第 2/4 条），无需再补。
3. R1：`notes/JIN_WISHART_THEOREM_TRACKER.md`（B0 的产出）建立后，S 可以把
   Python 侧的能力边界同步进去。—— **本轮已解锁**：B0 表已由 S 起草
   （`notes/JIN_WISHART_THEOREM_TRACKER.md`），Python 能力边界已同步入表；
   该表现归 C 做论文原文核验，S 后续只维护 Python 行与只读复查结论。

**给协调者（用户）**：

- 提交由协调者负责（C 的计划第 2 节第 6 条）。**当前未提交清单（S 第二轮
  从 `git status --short` 逐一核对，HEAD=5e48071e，2026-09-27 后）**：
  - 已修改未暂存：`infoq/` 四文件（P1/P2，+250/−41 行）、
    `notes/JIN_WISHART_EXECUTION_PLAN.md`、facade `JinWishartFormalization.lean`、
    `FourDimensionalPolarBridge.lean`、`NoncentralFourDimensionalCDF.lean`、
    `theory/jin_wishart_formalization/README.md`。
  - 未跟踪：`tests/`（5 个测试文件 + README + `__init__.py`）、
    `notes/AGENT_DIVISION_OF_LABOUR.md`（本文件）、
    `notes/JIN_WISHART_THEOREM_TRACKER.md`、
    `JinWishartFormalization/` 下 **29 个新模块**（`git status` 逐行列过：
    DeterminantRowExpansion、FinSpectralIndexCard、IndexedCourantFischerAttempt、
    IndexedCourantFischerProof、MIMOWishartSERExact、
    NoncentralFourDimensionalGaussianCDF、OrderedCourantFischerFiniteDim、
    OrderedEigenvalueFullMeasurable、OrderedEigenvalueWeyl、
    PaperSingleStreamTwoRowOutage、PaperSmallSideGram、PaperStatements、
    RepeatedRootNullSets、SixDimensionalAngularBesselI2、
    SpectralCoordinateSpanSupport、SpectralRayleighCoordinates、
    SpectralRayleighPrefix、SphereSixDAxialMeasure、SubspaceIntersectionFinrank、
    T3FixedCardinalityRowSelection、T4CentralOneColumnAnyRows、T4DensityToCDF、
    Theorem1TwoRowsActualCDF、TwoRowMeanGramSpectrum、TwoRowOutageScaling、
    TwoRowSampleCoordinates、TwoRowSmallOutageAsymptotic、WeylComplexHermitian、
    WeylRealSymmetric）、`.workbuddy/`、`.write_probe.tmp`、`.mimosa/`。
  - 另注意：facade 工作区版本现 import **82 个模块**（上一轮记录是 6 个新模块），
    与索引中的旧版不同——提交 Lean 新模块时必须把 facade 一起暂存。
    有 3 个模块**不在 facade 的 import 图里**但磁盘存在且单独构建通过：
    `FinSpectralIndexCard`、`MIMOWishartSERExact`、`SphereSixDAxialMeasure`
    （详见 8.5 节；是否并网由 C 决定，S 不介入）。
  - **建议分两次提交**：① Python 侧（`infoq/` 四文件 + `tests/` + 两份 notes）；
    ② Lean 侧（29 个新模块 + facade + README）。不要混入
    `.workbuddy/`、`.write_probe.tmp`、`.mimosa/`。
- `.write_probe.tmp` 是 S 探测写权限时留下的空文件，内容已标注"可安全删除"，
  但 S 的运行环境没有删除权限，需协调者处理。
- 429 限流：两个会话共享同一把 key，建议不要同时跑 `lake build`（输出极大，
  且 `.lake` 缓存并发写会互相干扰）。
- **环境备注（本轮）**：本机没有 Git Bash，StepCode 的 `run_command` 全程不可用
  （`node_repl` 同样故障）。S 已在 `.stepcode/config.toml` 顶部加了一行
  `shellPath = "D:\\MinGit\\usr\\bin\\sh.exe"`——该配置要重启 StepCode 才生效；
  重启后即可用 `run_command` 跑 git/python/lake。不需要时可删掉该行。

## 6. 交接模板（每张卡结束时填写，沿用 C 的计划第 8 节）

```text
任务卡 ID：
负责会话：
改动文件：
数学/语义陈述（含全部参数域）：
本次真正证明了什么；没有证明什么：
验证命令、退出码和关键输出：
新增的待审项：
Git 提交哈希（如未提交，原因）：
下一张卡及阻碍：
```

## 7. S 本轮交接（P2）

```text
任务卡 ID：P2
负责会话：S
改动文件：infoq/shannon_lp.py, infoq/converse.py, infoq/__init__.py,
          tests/test_shannon_lp_status.py
语义陈述：check() 返回四态 PROVED / NOT_IDENTIFIED / UNVERIFIED / SOLVER_ERROR。
          PROVED ⟺ 存在精确有理证书（元素不等式系数非负、向量恒等式精确成立）。
          目标恒为 0 时 [] 是合法空证书；None 表示复核失败。
本次真正修复了：LP 数值可行但证书复核失败时虚报 PROVED。
          求解器异常与"不在锥内"此前被混为 NOT_IDENTIFIED。
          移除了从未使用却暗示可调证明等级的 tol 参数。
没有做：未触及任何 Lean 文件；未改 README/AGENTS.md；未提交。
验证命令：D:\miniconda3\python.exe -m unittest discover -s tests -v
          退出码 0，Ran 105 tests, OK
          四个 demo 脚本另行验证均通过
新增待审项：tol 参数移除是公开 API 的破坏性变更，需 C 确认无调用方依赖。
Git 提交哈希：未提交（按计划由协调者统一提交）
下一张卡及阻碍：待用户/C 指派。S 建议下一步由 S 做 tests/README.md 补充，
          或等 C 完成 L3 后由 S 做一次独立的只读复查（不含修改）。
```

## 8. S 本轮交接（只读核验轮，2026-09-27 之后）

背景：用户指派 S"总结现状并完成所有应完成的任务"。本轮 S **不做任何行为变更**
（唯一例外：`infoq/shannon_lp.py` 两处纯文档修改），因为本机 shell 全部不可用
（无 Git Bash、`node_repl` 故障），无法跑 `unittest` / `lake build`，按纪律
"不能运行的验证不写进结论"，本轮定位为**只读核验 + 台账刷新**。

### 8.1 P1/P2 只读复核（通过）

逐行通读 `infoq/expr.py`、`shannon_lp.py`、`converse.py`、`__init__.py` 与
`tests/` 全部 5 个文件，确认：

- P1（expr.py）：`_parse_term` 是真乘法层；`*` 仅标量倍乘；隐式乘法/链式/
  带分数/括号标量/反向书写均在；`H(X)*H(Y)`、非零常数项、连续 `*`、`1/0`、
  保留字变量名全部抛 `ExprError`。与分工文件第 3 节记录一致。
- P2（shannon_lp.py）：四态齐全；`_rationalize_and_verify` 区分 `[]`/`None`；
  显式拒绝有理化后负系数；等式任一方向未核实整体不判 PROVED；
  `tol` 确已移除且有回归测试；`converse.format_report` 按状态分别计数。
  与分工文件第 3 节记录一致。
- 四个 demo 与 `experiments/blahut_arimoto.py` 均只用现行 API（`tol` 仅作为
  BA 迭代容差出现，与证明等级无关，不是漏网）。
- `tests/README.md` 的 P2 说明**已就位**（上一轮"待办 2"实际已完成）。
- **静态计数修正**：分工文件写"105 个用例"，本轮按 `def test_` 静态清点为
  **101**（test_expr 48 + test_shannon_lp 16 + test_shannon_lp_status 23 +
  test_numeric 8 + test_converse 6）。差额原因不明（可能上一轮后有过小幅增删），
  **以协调者实跑 `unittest discover` 的数字为准**。
- S 本轮的唯一改动：`shannon_lp.py` 模块 docstring 补四态说明、
  `ShannonResult.status` 行注释从"PROVED / NOT_IDENTIFIED"更新为四态
  （原注释是 P2 遗留的过时文本）。纯文档，零行为变更。

### 8.2 Lean 侧独立只读复查（L3 已完成后执行，按第 5 节约定）

- **占位符扫描**：`JinWishartFormalization/` 目录下 `sorry`/`admit`/`axiom`/
  `native_decide` **零命中**（`.lake/packages` 依赖里的命中与项目无关）。
- **facade 一致性**：`JinWishartFormalization.lean` 现 import 全部模块，含
  L3 四模块（`NuttallQ21Normalization`、`ScalarPhysicalScaling`、
  `NoncentralFourDimensionalPoissonMixture`、`OrderedEigenvalueMeasurable`）
  与 6 个未提交新模块。import 与磁盘文件一一对应，无缺失、无悬空。
- **M4 实际强度（重要更新）**：`Theorem1TwoRowsActualCDF.lean` 已超出
  2026-09-27 补记的"轴向特例"——`theorem1TwoRowsCandidate_eq_actualCDF` 与
  `theorem2TwoRowsCandidate_eq_actualCDF` 对**任意非零复均值** M 成立
  （非中心参数 = ‖mean‖²/2，x≥0），右边是真实样本
  `complexNoncentralSampleSmallestEigenvalue` 的 CDF；中心分支另有
  `...CentralCandidate_eq_actualCDF` 两条。即 **M2/M3/M4 的 `2×1` 闭环已闭合，
  只差人工测度审查**。
- **两处需要 C 明确的边界**（已写入台账，不是 S 的判断，是文件事实）：
  1. `TwoRowSmallOutageAsymptotic.lean` 目前**只有 private 引理**，公开的
     T4 渐近定理（F(x)/x² → exp(-λ)/2）尚未作为 public theorem 闭合；
  2. `OrderedEigenvalueWeyl.lean` 只证了 Weyl 连续性的前半（Rayleigh
     Lipschitz）， Courant–Fischer 半依赖 mathlib 缺失，G1 未闭合。
- `PaperStatements.lean` 是陈述层（Theorem 1–4 契约 + 依赖结构），其 docstring
  自称"只做陈述与结构"，与 `theory/README.md` 的措辞一致，**未发现夸大**。

### 8.3 本轮交接卡

```text
任务卡 ID：R1（独立只读复查）+ 台账刷新
负责会话：S
改动文件：notes/AGENT_DIVISION_OF_LABOUR.md（本文件）；
           infoq/shannon_lp.py（仅两处 docstring/注释，零行为变更）
数学/语义陈述：不涉及新数学内容。确认 P1/P2 语义与分工文件记录一致；
           Lean 侧 M2/M3/M4 的 2×1 闭环对任意非零复均值已闭合。
本次真正做了什么：通读 infoq 四文件与 tests/ 五文件并逐条核对；
           扫描项目自有 Lean 目录占位符（零命中）；
           核对 facade import 与未提交文件清单（据 .git/index 解析）；
           修正 tests/README.md 与用例计数两处台账误差；
           刷新所有权表、任务卡表、未提交清单。
没有做什么：没有运行任何测试或构建（shell 不可用，按纪律不虚构验证输出）；
           没有碰任何 Lean 文件；没有提交；没有删 .write_probe.tmp。
验证命令、退出码和关键输出：本轮无法执行（见上）。需协调者补跑：
           D:\miniconda3\python.exe -m unittest discover -s tests -v
           D:\miniconda3\python.exe verification\demo_shannon_lp.py
           D:\miniconda3\python.exe verification\demo_numeric_oracle.py
           D:\miniconda3\python.exe verification\demo_converse_check.py
           D:\miniconda3\python.exe experiments\blahut_arimoto.py
           & 'D:\vibe math\.tools\elan\bin\lake.exe' build JinWishartFormalization --quiet
新增待审项：① M2/M3/M4 的 2×1 闭环需人工测度审查（Fubini/换元/参数对应）；
           ② TwoRowSmallOutageAsymptotic 公开定理未闭合（C 的在建卡）；
           ③ 根 README.md 的 infoq 速查仍只写两态，未反映 P2 四态
              （README 归协调者，S 不改）。
Git 提交哈希：未提交（按计划由协调者统一提交；建议分 Python / Lean 两次，见第 5 节）
下一张卡及阻碍：B0（C）建 notes/JIN_WISHART_THEOREM_TRACKER.md 后，
           S 把 8.4 节文本同步进去；在 B0 建成前 R1 的同步项保持阻塞。
```

### 8.4 待同步进 B0 追踪表的 Python 侧能力边界（C 建表时直接粘贴）

```text
[infoq 能力边界 — 2026-09-27 后 S 会话核验]
- infoq.check 四态：PROVED（精确有理证书，无条件证明）/ NOT_IDENTIFIED
  （已证不在 Shannon 锥内，≠命题为假）/ UNVERIFIED（LP 数值可行但证书复核
  失败，只是数值证据）/ SOLVER_ERROR（求解器未正常结束）。
- 约束：马尔可夫链 "X-Y-Z"（自动展开成对条件独立）与一般等式 "I(X;Z|Y) = 0"。
- 语法：H(X,Y)、H(X|Y,Z)、I(X;Y)、I(X1,X2;Y|Z)；标量倍乘 *（可省略）、
  分数系数；禁止信息量相乘与非零常数项。
- 已知非 Shannon 型（NOT_IDENTIFIED 属预期）：Ingleton、Zhang-Yeung 1998。
- 数值预言机（infoq.Oracle）：随机采样 + Nelder-Mead 精修，输出 gap /
  counterexample / tight；**数值证据不是证明**，紧而不等的假命题数值上
  可能漏检。
- 测试：tests/ 五个文件，静态 101 个用例（协调者实跑数以 unittest 输出为准）。
- 边界：Shannon 锥只覆盖元素不等式组合；非 Shannon 型命题、测度论步骤、
  极限交换均超出 LP 能力，必须人工/其他工具。
```

### 8.5 第二轮只读核验（2026-09-27 后，shell 恢复，实跑测试与构建）

本轮 S **未修改任何 Lean 文件、未修改 infoq 行为代码**；唯一改动是本台账
文件自身。所有结论来自本轮实跑命令。

**Python 侧（S 的所有物）**：

- `D:\miniconda3\python.exe -m unittest discover -s tests` → `Ran 105 tests, OK`。
  **这解决了 8.1 节的计数疑问：实跑就是 105**（静态清点 101 少算了
  mock 分支用例，上一轮的差额原因至此确认，以 105 为准）。
- 四个 demo 全部退出码 0：`verification/demo_shannon_lp.py`、
  `demo_numeric_oracle.py`、`demo_converse_check.py`、
  `experiments/blahut_arimoto.py`。
- `git diff --stat -- infoq/` = +250/−41（四文件），与 P1/P2 记录一致。

**Lean 侧（C 的所有物，S 只读核验）**：

- `lake build JinWishartFormalization --quiet` → **退出码 0**。注意输出几乎全是
  `Replayed`：`.lake/build/lib/lean/JinWishartFormalization/` 下已有 86 个
  olean，即 C 此前已构建过，本轮是缓存重放 + 全量复核通过。（8.2 节曾据
  `.lake/build/lib` 无项目目录判断"从未构建过"，**那个判断有误**：
  项目 olean 在 `build/lib/lean/` 下一层，特此更正。）
- 规模（本轮快照 19:27）：91 个模块、13,695 行、483 个 theorem/lemma 声明。
  （8.2 节之后的增长：C 当晚 18:36–19:25 连续写入，快照从 89 模块/12,990 行/
  473 声明增至 91/13,695/483。**本台账所有计数必须带时间戳**，工作区是活的。）
  `sorry`/`admit`/`axiom`/`native_decide` 在项目自有文件中**零命中**
  （findstr 与 PowerShell 双通道复核）。
- facade 直接 import 84 个模块，无悬空 import；5 个叶子模块无人引用：
  `FinSpectralIndexCard`、`MIMOWishartSERExact`、`MvPolynomialZeroSetNull`、
  `PaperStatements`、`SphereSixDAxialMeasure`。其中
  `SphereSixDAxialMeasure` 单独构建通过；`FinSpectralIndexCard` 与
  `MIMOWishartSERExact` 当时用 `lake build <module>` 判定"通过"——
  **该判定方法有缺陷**（cmd 的 `%errorlevel%` 经管道后拿到的是 findstr 的退出码，
  不是 lake 的），20:20 用 `lake env lean` + `&&/||` 复验实为 **FAIL**，见 10.6 节；
  `MvPolynomialZeroSetNull` 当时是 C 19:20 的 WIP（有真实编译错误），后由 C 于
  19:43 修好；`PaperStatements` 是陈述层契约，按设计等 G2/G3 来填充。
  **教训：模块级验证一律用 `lake env lean <file> && echo OK || echo FAIL`，
  不要用管道后取 `%errorlevel%`。**
- 8.2 节曾把 `OrderedCourantFischerFiniteDim` 与 `SpectralCoordinateSpanSupport`
  疑为游离模块，实际已被 `IndexedCourantFischerProof`/`WeylComplexHermitian`/
  `WeylRealSymmetric` 传递 import，**不是游离模块**（上一条的叶子清单以
  `experiments/lean_import_graph.py` 的依赖图计算为准）。
- **对 8.2 节边界的更新**：`TwoRowSmallOutageAsymptotic.lean` 现在有
  **两条公开定理**（`noncentralTwoRowCDF_div_tendsto_exp_neg_noncentrality_half`
  与 `..._anyMean` 任意复均值版），T4 的 `2×1` 渐近已闭合为 public theorem；
  该文件此前"只有 private 引理"的记录过期。
- `2×1` 闭环复核（读陈述确认）：`Theorem1TwoRowsActualCDF.lean` 含
  `theorem1/2TwoRowsCandidate_eq_actualCDF`（任意非零复均值）、
  `...eq_actualLargestCDF`、中心分支两条；`PaperSingleStreamTwoRowOutage.lean`
  含论文物理参数映射（`paperScatterEpsilon`、
  `paperTwoRowWeakOutage_highSNR_limit` 等）。
- 未做：未读论文 PDF 核对（B0 归 C）；未做任何人工测度审查；未提交。

## 9. 整体进度百分比（2026-09-27 后 S 会话估算，供协调者排期）

口径：执行计划第 0 节的五维验收（陈述/基础设施/模型→公式/公式→结论/审查）；
总体按剩余工作量加权，**一般维度（G1–G4）是全书主体，也是剩余工作量的大头**。

| 工作流 | 进度 | 依据 |
|---|---|---|
| Python 机检工具链（P1+P2） | **100%** | 四态语义、解析器、测试（实跑 105 全绿）、demo、README 均就位（未提交） |
| Lean 模块修复与整合（L1+L2+L3） | **100%** | 四模块全部单独构建通过并并入 facade |
| `2×1` 闭环（M1–M4） | **~90%** | 陈述+证明已闭合到任意非零复均值（T1/T2 候选=真实 CDF，T4 渐近 public）；欠人工测度审查 |
| 一般维度（G1–G4，论文主体） | **~15%** | G1 谱可测已闭合（Courant–Fischer min-max + Weyl + 小侧 Gram）；T3 泛型固定基数行选择恒等式、T4 密度→CDF 抽象引理已证；联合密度（G2）与一般 T1–T3 等式（G3）未开始 |
| 台账/文档/独立审查（R1） | **~85%** | B0 表已建（待 C 核验）、theory/README 详尽、独立只读复查已做两轮（第二轮实跑测试+构建） |
| **总体（按工作量加权）** | **~30%** | 基础设施与特例已牢，主体定理（一般维度 Theorem 1–4 的概率等式）尚未开始 |

**解读**：距离"全文形式化"的成功标准，剩余核心是 G2（联合密度与测度变换）→
G3（一般 Theorem 1–3 等式）→ G4（Theorem 4/SER 封闭）+ 全部
`[需人工审查]` 项的独立测度论审查。`2×1` 闭环**不能**外推为总体完成度。

## 10. 第三轮分工提案（2026-09-27 晚，S 起草，待 C 与协调者确认）

### 10.1 为什么重划

- C 已进入 G2 关键路径（当晚 18:36–19:25 连续写入 `T4DensityToCDF`、
  `RepeatedRootNullSets`、`SixDimensionalAngularBesselI2`、`PaperSmallSideGram`、
  `T3PaperThetaSpecialization`、`MvPolynomialZeroSetNull`），主线只剩它自己
  能碰的 Lean 证明。
- 计划书第 6 节末的 P4 审计要求**先收紧 `PaperStatements` 契约**（补
  probability-measure 连接、参数域、T3 的 (23)–(25) 概率项、T4 的 PDF 首项、
  SER/outage 的 (35)–(45) 结构），否则 G3/G4 会建在过弱占位上。这是 C 的前置卡。
- S 的 Python 卡（P1/P2）已 100%，原分工里 S 只剩 R1 只读复查，工作量不饱和；
  而 C 的路径上**没有可安全并行的部分**（测度论证明必须串行——沿用计划书
  第 3 节结论，S 同意且不介入）。
- 因此原则一句话：**C 独占 Lean 主线；S 接管所有零文件碰撞的支撑面**
  （验证机械化、数值对照、文档与提交卫生）。

### 10.2 文件所有权（新增项标 ⭐，需协调者批准）

| 文件 / 目录 | 所有者 | 说明 |
|---|---|---|
| `infoq/**`、`tests/**` | **S** | 不变 |
| `theory/jin_wishart_formalization/**`、`notes/JIN_WISHART_EXECUTION_PLAN.md` | **C** | 不变，S 只读 |
| `notes/AGENT_DIVISION_OF_LABOUR.md` | **S** | 不变（本文件） |
| ⭐ `experiments/`（除既有 `blahut_arimoto.py`） | **S** | 数值实验新文件；本轮已建 2 个（见 10.4） |
| ⭐ `verification/` | **S** 写、C 可读 | 此前未划归 |
| `notes/JIN_WISHART_THEOREM_TRACKER.md` | S 维护 Python 行与只读结论 | 论文行最终核验权仍归 C（不变） |
| `README.md`、`AGENTS.md` | 协调者（用户） | 不变 |

### 10.3 任务卡（新编号 S*，与 C 的 B0/P/L/M/G/R 不冲突）

| 卡 | 内容 | 负责 | 状态 |
|---|---|---|---|
| **S1** | 验证轮机械化：import 图核对 + 占位符扫描 + 时点构建 + 快照记录 | S | ✅ 首轮完成（8.5 节）；工具 `experiments/lean_import_graph.py` 已建 |
| **S2** | 数值对照通道：对 C 每个已闭合的 Lean 特例做 Monte Carlo 独立验证 | S | ✅ 首张交付 `experiments/jin_wishart_mc_check.py`（结果见 10.4） |
| **S3** | B0 二轮：论文原文 `[待核实]` 项提取（记号映射表） | S 起草、C 核验 | ⬜ 待 C 确认是否重复劳动（C 已能访问 arXiv v2 并按 (23)–(25)/(48) 核对过） |
| **S4** | 文档卫生：根 README 四态速查草案、提交分段清单 | S 草案、协调者落盘 | ⬜ 草案在协调者点头后写 |
| C 侧 | G2 → G3 → G4 主线；P4 契约收紧为 G3/G4 前置 | C | 进行中；WIP 不记完成 |

### 10.4 S2 首张结果（2026-09-27 晚，seed 20260927，n=4×10⁶/估计）

- **对照组全部吻合**：中心 `m×1`（m=1,2,3,5）对 scipy `Gamma(m,1)`；非中心
  `2×1`（λ=0.5,2,5）对 scipy `ncx2(4, 2λ)/2`——25 个点全部在 4σ 内。这独立
  确认了 Lean 的方差约定（复条目单位方差）与非中心参数 `λ=‖M‖²_F` 的整条映射链，
  与 `TwoRowSampleCoordinates`/`Theorem1TwoRowsActualCDF` 的陈述一致。
- **极限项全部通过**：中心硬边 `F/x^m → 1/m!`（m=1: 0.996±0.005；
  m=2: 0.948±0.034）；非中心 `2×1` 硬边 `F/x² → (1/2)e^{−λ}`
  （λ=0.5: 1.004±0.018；λ=2: 1.055±0.040）。
- **纪律声明**：数值证据不是证明（AGENTS.md 铁律 3）。本通道的作用是在特例被
  推广到一般维度之前抓陈述/参数映射错误，并给已证特例一个独立佐证；Lean 证书
  才是证明。
- 复现：`D:\miniconda3\python.exe experiments/jin_wishart_mc_check.py`。
- 已知边界：m≥3 的中心硬边事件在可用 x 上太稀有，直接极限不可分辨，由对照组
  （Gamma 识别）+ 解析极限覆盖；一般 s>1 多列联合分布**没有**数值对照，
  等 G2 的联合密度出来后再补。

### 10.5 并行硬规则（两 agent 同一工作区）

1. 文件所有权边界不变（10.2）；越界即冲突，先在本文件登记再动。
2. **构建避让**：任何一方跑 `lake build`（写 `.lake`）前在本文件记
   `BUILD START <时间>`，结束记 `BUILD END <时间>`；S 日常核查只用
   `lake env lean <file>`（只读，不写缓存）。
3. **快照纪律**：工作区是活的（今晚 19:18–19:25 C 连续写入），所有核对结论必须
   带时间戳与计数；计数过期不修补，只加新快照。
4. **WIP 不记完成**：未接入 facade 或编译失败的文件（如当前
   `MvPolynomialZeroSetNull`）在台账标 WIP，"文件存在"≠"已证"。
5. **里程碑公告**：C 每完成一卡在计划书追加一行（现有做法不变）；S 看到后跑一轮
   S1，结果写入本文件 8.x。
6. **提交仍由协调者独占**；两段式（Python / Lean），排除 `.workbuddy/`、
   `.write_probe.tmp`、`.mimosa/`。

### 10.6 第四轮：C 停产后主线转交 S（2026-09-27 20:00，协调者指派）

- C 的最后写入是 **19:57:03**（`T3NormalizationAudit.lean`）。20:12–20:20 S 复验发现
  C 停在未完成状态，留下 **4 个编译失败的叶子模块**：
  `FinSpectralIndexCard`（13/19 行类型不匹配）、`MIMOWishartSERExact`、
  `MvPolynomialGramTwoByTwo`（19:55 新建）、`T3NormalizationAudit`（19:57 新建）。
  已交付子 agent 修复（stage ②）。`MvPolynomialZeroSetNull.lean` 已被 C 于 19:43
  修好并经 S 复验通过（`lake env lean` 退出码 0），且已被 C 接入某模块（不再是叶子）。
- 协调者指派 S 接管 Lean 主线。所有权变更见第 1 节；S 的 Lean 进展记入本文件，
  **不改写 C 的计划书**（保持 C 的审计轨迹完整）。
- 本轮按协调者建议开三个并行 stage：
  | stage | 内容 | 执行者 |
  |---|---|---|
  | ① 外部检索 | mathlib 现有引理/外部 Wishart 形式化库/论文方程号核对 | 子 agent（只读+联网） |
  | ② 形式化推进-修复 | 修复 C 遗留的 4 个坏叶子模块 | 子 agent（只写这 4 个文件） |
  | ③ 规划 | G2 联合密度的分步证明计划 + mathlib 资产盘点 | 子 agent（只读） |
  | ④ 形式化推进-主攻 | S 自己写 `WishartSimpleSpectrum.lean`（G2 的"谱简根几乎必然"砖） | S |
- 并行铁律（对子 agent 同样生效）：**只许 `lake env lean <file>` 检查，禁止
  `lake build`**（避免 .lake 缓存并发写）；每个子 agent 只写自己那几个文件；
  facade 并入与全量构建由 S 统一做。

### 10.7 S 主攻交付：`WishartSimpleSpectrum.lean`（2026-09-27 晚，任意维度重根零测）

**新模块**（S 写，已接入 facade，`lake env lean` 退出码 0）：

```
WishartSimpleSpectrum.lean
  genericResultant_eval        : 通用矩阵的判别式多项式在矩阵坐标处的取值
                                  = 该矩阵特征多项式对其导式的 resultant
  resultant_eq_zero_of_common_root : 多项式引理（公共根 ⟹ resultant = 0）
  genericResultant_ne_zero     : 通用 resultant 是非零多项式
                                 （对角见证矩阵 + separable_prod_X_sub_C_iff）
  repeated_root_set_null       : 特征多项式有重根的 d×d 实矩阵集合 Lebesgue 零测
                                 （任意 d，复用 MvPolynomialZeroSetNull）
```

**意义**：这是 G2"重根零测"砖的**任意维度**版本，把 C 的 2×2 原型
`MvPolynomialGramTwoByTwo.lean`（96 行，只处理 2×2）推广到任意 d。
技术要点：不走 `Matrix.discr`（mathlib 只有 2/3 次的判别式引理），改用
`resultant`（有 `resultant_map_map` 函子性）+ `separable_prod_X_sub_C_iff`
（对角见证 ⟹ 特征多项式可分 ⟹ 与导数互素 ⟹ resultant ≠ 0）。G2 规划
（stage③）曾把一般 d 的这一步估为"中偏难、需自证 150–250 行判别式-无重根桥"，
resultant 路线实际绕开了该缺口。

**没有证明的（诚实边界）**：
1. **复 Hermitian 情形未做**——论文的 Gram 是复 Hermitian 矩阵，本模块只做实矩阵。
   复版需要把通用 resultant 拆实部/虚部（或在 `Complex (MvPolynomial …)` 上建
   通用 Hermitian 矩阵并证其特征多项式系数自共轭），是明确的下一步。
2. 未连到 `OrderedEigenvalueLaw.strictAnti_ae`（PaperStatements 契约字段）——
   需要"重根 ⟺ 非严格降序"的谱定理桥（Hermitian 特征值理论）。
3. 未连 Wishart 样本律（G2 的联合密度仍完全开放）。
4. 本模块自身**不含** Fubini/换元步骤（只有集合包含与测度单调性）；
   底层零测引理的 Tonelli 步骤仍归 C 的 `[需人工审查]` 清单。
