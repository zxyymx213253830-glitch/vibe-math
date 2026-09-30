# 金石论文形式化与仓库修复：逐项执行任务书

更新日期：2026-09-26。工作目录：`D:\vibe math`。本文写给可以反复运行、但单次上下文和推理预算较小的执行 AI。每次只做一张任务卡；完成验证、记录结果、提交后再领取下一张。本文是执行计划，不表示论文已经完整形式化。

## 0. 目标、边界和成功标准

最终目标是把本仓库选定的金石早期 Wishart 矩阵特征值论文中的定理及其实际概率模型，在 Lean 中逐项、无漏洞地形式化。先完成可控的单列/单特征值情形，再推进多特征值一般情形。同时修复 `infoq` 工具的语义问题，以免研究工作被错误的“已证明”状态误导。

“完整形式化”必须满足：论文各定理的假设、参数域、随机模型和结论有逐条对应的 Lean 陈述；每条证明通过项目构建；关键随机变量确实定义为论文中的模型，不只是一个形状相似的候选密度或特殊函数恒等式；无 `sorry`、`admit`、新公理或把待证结论塞进假设；测度论环节经独立审查。只证明 `1×1`、`2×1` 或“公式侧”不算全文完成。

不要把“所有源文件能够编译”与“论文定理已经证明”混为一谈。验收表应分别记录：`数学陈述已对齐`、`所需基础设施已构建`、`模型到公式已证明`、`公式到论文结论已证明`、`独立审查已通过`。

## 1. 已核验的起点（不是待办清单）

以下仅是 2026-09-26 工作区快照；每个新执行回合先重新核验，不能把它当成永恒事实。

| 项目 | 已核验状态 | 重要限制 |
| --- | --- | --- |
| Git | `HEAD` 为 `2cad71b`；工作区非干净 | 已有修改属于用户，不可重置或整体清理 |
| Python 解析器 | `infoq/expr.py` 有未提交的乘法/除法解析修补 | 先审查与补测试，不要从零重写 |
| Python 测试 | `D:\miniconda3\python.exe -m unittest discover -s tests -v`：82 个通过 | `tests/` 未跟踪；需审查测试质量并纳入版本管理 |
| Lean 主工程 | 在 `theory/jin_wishart_formalization` 执行 `lake build JinWishartFormalization --quiet` 通过 | 主入口尚未导入下面四个游离模块 |
| 游离 Lean 模块 | `NoncentralFourDimensionalPoissonMixture`、`OrderedEigenvalueMeasurable` 单独构建通过 | 前者只是候选径向核的点态混合；后者目前只覆盖最大/最小特征值的可测性 |
| 另外两个 Lean 模块 | `NuttallQ21Normalization`、`ScalarPhysicalScaling` 单独构建失败 | 具体错误见任务卡 L1/L2，不可标为完成 |
| LP 判定器 | `infoq/shannon_lp.py` 存在精确证书失败后仍返回 `PROVED` 的分支 | 是 P0 正确性问题，现有 82 个测试未覆盖该失败分支 |

当前未跟踪内容包括 `tests/`、四个上述 Lean 模块、`.workbuddy/`、`.write_probe.tmp`；`infoq/expr.py` 已修改。不要执行 `git clean`、`reset --hard` 或批量提交这些文件。`.workbuddy/`、`.write_probe.tmp` 的归属不明，未经用户同意不删除、不忽略。

外部 AI 的评估有参考价值，但两处必须纠正：一是解析器补丁和 82 个测试已经存在；二是 `I(X;Y)=I(Y;X)` 一类零目标的**空证书可以有效**，不能用“证书列表为空”证明 LP 有 bug。真正的 bug 是证书生成失败时返回 `(None, None)`，而上层仍把状态设为 `PROVED`。必须区分 `None` 和 `[]`。

## 2. 执行总规则

1. 每次只领取下文一张卡，先读相关文件和 `AGENTS.md`，写出将要改动的文件列表；不顺手重构其他模块。
2. 起手运行 `git status --short`，确认本次改动与已有脏工作区的边界。不能覆盖、恢复或提交不属于本卡的变更。如边界不可判定，停下向用户确认。
3. 修改源文件只用 `apply_patch`。每一步先建局部证明/测试，再做模块集成，最后运行全局验证。不得以 `sorry`、`admit`、新增公理、`native_decide` 代替分析证明。
4. 数值实验只用于寻找反例或检查公式，固定种子并与已知结果对照；不能作为 Lean 等式或概率恒等式的证明。
5. 可测性、Fubini/Tonelli、换元、极限交换、正则性和异常点处理在研究记录中标 `[需人工审查]`；即使 Lean 通过，也检查形式化陈述是否弱于论文原命题。
6. 每张卡完成时留下：改动摘要、确切验证命令及退出码、尚存数学缺口、下一卡建议。每个可运行状态单独提交；只暂存本卡文件，避免把未知的用户文件混入提交。
7. 同一子目标连续三次不同尝试仍不收敛时，保留可运行状态，写下最小失败目标、已试引理和下一步数学问题，交给更强模型或人工；不要循环生成随机 tactic。

建议环境变量不依赖旧终端 PATH：Python 一律用 `D:\miniconda3\python.exe`；Lean 用 `D:\vibe math\.tools\elan\bin\lake.exe`，工作目录为 `D:\vibe math\theory\jin_wishart_formalization`。从 PowerShell 调用带空格路径时使用 `& '完整路径'`。

## 3. 优先级和依赖

| 顺序 | 卡片 | 前置 | 可交付结果 |
| --- | --- | --- | --- |
| 0 | B0 | 无 | 基线、定理对照表和脏工作区清单 |
| 1 | P1 | B0 | 已有解析器补丁经审查、测试、单独提交 |
| 2 | P2 | B0 | LP 状态不再虚报 `PROVED`，失败分支有测试 |
| 3 | L1、L2 | B0 | 两个失败模块分别单独构建通过 |
| 4 | L3 | L1、L2 | 四个游离模块按真实能力分批并入入口 |
| 5 | M1 → M2 → M3 → M4 | L1、L3；M2 依赖 M1 | `2×1` 真实非中心模型的定理 1/2 闭环 |
| 6 | G1 → G2 → G3 → G4 | M4；独立数学审查 | 多特征值一般情形及其余定理 |
| 全程 | R1 | 各卡完成后 | 台账、文档、独立审查和可重复构建 |

P1、P2、L1、L2 可以由不同执行者在**不同文件**上并行，但共享工作区中由协调者负责提交、检查冲突。M1 之后的测度论证明宜串行，因为结论高度依赖前一环节的精确定义。

## 4. 基线与 Python P0 任务卡

### B0 — 固定基线与论文定理对照

- 输入：`notes/jin_2006_wishart_summary.md`、`theory/jin_wishart_formalization/README.md`、Lean 主入口、现有论文 PDF/出处及仓库中已保存的研究材料。
- 动作：建立一张定理追踪表（建议 `notes/JIN_WISHART_THEOREM_TRACKER.md`），每行写论文定理编号、原文假设/参数范围、概率模型、原结论、对应 Lean theorem 全名、状态（`未陈述/仅公式侧/已证明模型桥/已证明结论/审查通过`）、缺口及证据。不能凭文件名猜定理内容；论文原文无法访问时标 `[待核实]` 并停止声称逐条对齐。
- 验收：表中显式区分中心/非中心、单特征值/多特征值、归一化/物理尺度、零参数/正参数边界；`git status --short` 记录在交接说明；提交只含新追踪表。

### P1 — 审核已有表达式解析器补丁

- 输入：已修改的 `infoq/expr.py` 和未跟踪的 `tests/`；先阅读 `git diff -- infoq/expr.py`、`tests/README.md`。
- 核对：显式/隐式标量乘法（如 `2*I(X;Y)`、`2I(X;Y)`）、有理系数、括号、除以非零标量、表达式末尾、非法两个信息量相乘、零分母、负号和运算优先级。不要添加信息量之间的非线性乘法。
- 补测：解析后规范线性系数与手写 `Fraction` 向量完全一致；非法语法明确失败。已有测试若覆盖则引用测试名，不重复造大量近似案例。
- 验收：`D:\miniconda3\python.exe -m unittest discover -s tests -v` 全通过；新增测试不改变旧合法表达式结果；对 `infoq/expr.py` 和选定的 `tests/` 文件进行有界暂存、独立提交。切勿把 `.workbuddy/` 或 `.write_probe.tmp` 混入。

### P2 — 修复 LP “无精确证书却 PROVED”

- 输入：`infoq/shannon_lp.py`、`infoq/converse.py`、`infoq/__init__.py`、对应测试及 API 文档。
- 设计：引入清晰的 `UNVERIFIED`（或 `NUMERICALLY_FEASIBLE_UNVERIFIED`，二选一并统一）状态。`PROVED` 只在有精确有理证书、各系数非负、向量恒等式精确成立时返回。若目标恰为零，`[]` 是可接受的精确空证书；`None` 表示失败，绝不能混淆。
- 分支检查：`linprog` 数值成功但有理化/精确复核失败 → `UNVERIFIED`；`linprog` 真正证明不可行（核对求解器状态 `2` 及数学语义）与迭代/数值错误（`1/3/4`）分开；等式由双向不等式构成时，只要任一方向未核实，就不能返回已证明。审查 `tol` 参数是使用、移除还是明确文档化，不要让它暗中决定证明等级。
- 测试：用 `unittest.mock.patch` 定向模拟 `_rationalize_and_verify` 返回 `(None, None)`，断言不是 `PROVED`；保留零目标空证书有效的测试；加非负系数检查、求解器非正常状态、等式状态传播。不要只靠随机 LP 测试触发罕见分支。
- 验收：所有 `PROVED` 输出可通过独立的有理数证书校验；全部测试通过；`infoq` 使用文档和 `converse` 报告明确新区分；仅提交本卡文件。若需改变公开 API，先列出兼容影响。

## 5. Lean 现有模块修复任务卡

### L1 — `NuttallQ21Normalization` 单文件修复

- 文件：`theory/jin_wishart_formalization/JinWishartFormalization/NuttallQ21Normalization.lean`。
- 现状：单独构建在约第 156 行 `rw [pow_succ]` 失败（表达式结构与重写模式不符），约第 181 行 `positivity` 不能关闭目标。先重新取得实际错误行号，不要盲改旧行号。
- 方法：把多项式幂与系数等式拆成单独 `calc`，优先使用 `ring`、`ring_nf`、`pow_succ` 的定向重写及明确的正性引理；积分证明只在所需条件齐全时接上。保存原 theorem 陈述，若发现陈述错误先报告具体反例/类型障碍。
- 验收：`& 'D:\vibe math\.tools\elan\bin\lake.exe' build JinWishartFormalization.NuttallQ21Normalization --quiet` 退出码 0；证明无占位。随后另立桥接引理，证明实积分表达式确实等于项目中复参数版本的 `nuttallQ 2 1 a 0 = a`（注明 `a` 的参数域）。仅有实积分恒等式不等于已经证明 `2×1` CDF。

### L2 — `ScalarPhysicalScaling` 单文件修复

- 文件：`theory/jin_wishart_formalization/JinWishartFormalization/ScalarPhysicalScaling.lean`。
- 现状：约第 35 行 `rw [Real.norm_eq_abs, sq_abs]` 没有匹配模式。重新读取当前目标；从 `ε>0` 推出 `ε≠0` 与 `|ε|=ε`，再用 `field_simp`/`ring` 或合适范数平方引理处理乘积。
- 验收：单独 `lake build JinWishartFormalization.ScalarPhysicalScaling --quiet` 退出码 0；特意检查 `ε=0` 不被错误纳入正尺度结论。本模块只给确定性标量变换，不能因此宣称一般协方差模型已完成。

### L3 — 合并四个游离模块但不夸大陈述

- 输入：上述 L1/L2，以及已经能单独构建的 `NoncentralFourDimensionalPoissonMixture.lean`、`OrderedEigenvalueMeasurable.lean`；主入口 `JinWishartFormalization.lean`。
- 动作：逐个审阅 theorem 的实际类型，再一次导入一个模块并运行主构建。出现重名或循环依赖时先重命名局部 theorem/调整 import，勿一次性引入所有内容。必要时同步 README 的“已编译/尚未建立的桥”。
- 语义警戒：Poisson 模块目前证明的是**候选径向核**的点态混合，不是非中心高斯向量的实际分布。可测性模块目前仅覆盖最大/最小特征值，不等于内部排序特征值全部可测。
- 验收：四模块各自及 `lake build JinWishartFormalization --quiet` 均通过；README 清楚说明这两处能力边界；无占位证明。任何模块若数学陈述仍待修正，可暂不导入，但必须在追踪表注明原因，不以绿色构建掩盖。

## 6. `2×1` 非中心实际模型闭环任务卡

目标不是再证明一个形似论文公式的表达式，而是从项目中定义的复高斯随机向量出发，证明其最大/唯一特征值的 CDF 与论文特例一致。参数符号必须由 B0 的对照表固定；下述 (a,t,r,x) 仅指局部证明变量，不预设论文的归一化。

### M1 — 精确陈述球面推前分布

- 新建一个职责单一的 Lean 模块，例如 `NoncentralSphereCoordinateLaw.lean`。先定义 `S³` 上目标坐标映射（与均值方向的实内积或所用角度坐标），明确球面测度是表面积测度还是概率测度。
- 目标恒等式需由选定的归一化推出：未归一化表面积测度在 `t∈[-1,1]` 的密度候选为 `4π√(1-t²)`，总质量 `2π²`；若用概率测度应除以 `2π²`。系数需由当前 Lean 测度定义核对，不许直接抄公式。
- 先证明弱版本：对有界连续或非负可测测试函数的积分恒等式；再推出所需具体指数/径向 integrand。明列端点、零范数、旋转不变性、可积性。与已有四维极坐标分解对接，不重复定义冲突的测度。
- 验收：所有公式两边类型和测度一致，质量检验通过；局部构建通过；研究记录标 `[需人工审查]`，请不同执行者审查 Jacobian、异常点和旋转论证。

### M2 — 从真实高斯律到径向密度

- 前置：M1 和已构建的四维极坐标引理、候选 Poisson 混合引理。
- 从实际 `2×1` 复高斯向量及其均值/方差定义出发，严格证明平方范数（即唯一非零特征值）事件的概率等于径向积分。证明时逐项标注密度的正规化、平移后的指数项、球面角积分、Tonelli/Fubini 的非负或可积条件。
- 再证明该径向积分等于现有候选 Poisson 混合；不能把候选混合的定义直接指定为随机变量的分布。若零均值分支需极限交换，优先独立证明零均值情形，避免无证明的连续极限。
- 验收：theorem 的左边必须是实际随机变量事件的测度，右边才是论文公式/混合表示；`λ>0`、`x≥0` 等参数域写在陈述中；局部构建和主构建通过；独立测度审查完成。

### M3 — 特殊函数正规化和边界

- 前置：L1、M2。把实积分版 Q21 恒等式与项目中的复参数 `nuttallQ` 定义桥接，检查 `a=0`、`x=0`、`x<0`、正尺度变换。证明 CDF 的 `0≤F≤1` 和必要的极限，避免只得到形式上相等却未归一化的表达式。
- 验收：每一处乘法常数和 Gaussian 方差约定与 B0 定理对照一致；有闭式或已知中心极限作 sanity check，但此检查不替代证明。

### M4 — 论文 `2×1` 定理 1/2 对应与审稿

- 写两个“封面 theorem”：分别使用论文定理 1、2 在 `2×1` 特例中的陈述，调用 M2/M3 得到结论。若二者在单特征值时重合，显式写出该等价的原因，不复制证明。
- 用独立审查者检查：假设是否与论文一致、分布是否真实、公式是否强度足够、是否遗漏零参数/尺度边界。审查发现的问题逐条进入追踪表，不用措辞模糊的“基本完成”。
- 验收：封面 theorem 构建通过，追踪表中对应行达到“审查通过”；README 只能写“`2×1` 特例完成”，不得写“全文完成”。

### 执行状态补记（2026-09-27，C）

- 已新增 `FourDimensionalPolarBridge.lean` 中实际四维平移高斯球积分的极坐标/Fubini 桥，
  并在 `NoncentralFourDimensionalCDF.lean` 中把该积分严格化为真实四维轴向高斯球概率的
  `1 - Re(Q₂,₁(a,R)/a)`。其所需有界支撑与可积性已由 Lean 检查；球面测度参数化、Fubini
  与极坐标 Jacobian 的数学对应仍标 `[需人工审查]`。
- `NoncentralFourDimensionalGaussianCDF.lean` 进一步证明 Mathlib 的四维 `stdGaussian`
  球概率等于该 Q 公式。`TwoRowSampleCoordinates.lean` 将实际 `ComplexSample (2×1)`
  通过保范等距映射送至 `Fin 4`，并显式补偿复坐标编码的 `√2` 尺度。
- `Theorem1TwoRowsActualCDF.lean` 已证明一个受限但真实的论文模型结论：均值矩阵只有
  `(0,0)` 的实分量非零、且 `|M₀₀|²=λ>0` 时，Theorem 1 的 `(1,2,1)` 公式候选等于
  实际单列非中心 Wishart 唯一特征值的 CDF（`x≥0`）。这把 M2/M3/M4 推进到轴向特例，
  同一模块也证明 Theorem 2 的 `(1,2,1)` 公式候选给出同一真实 CDF，明确利用单列只有
  一个 Gram 特征值，故最大与最小特征值一致。零非中心参数已通过论文 `L=0` 的中心
  分支另行接到实际 CDF；正参数两条定理仍都不覆盖一般复均值方向，也未完成人工测度
  审查。
- 验证：在 `theory/jin_wishart_formalization` 中运行
  `lake env lean JinWishartFormalization/TwoRowSampleCoordinates.lean`、
  `lake env lean JinWishartFormalization/Theorem1TwoRowsActualCDF.lean` 均退出码 0；
  接入 facade 后 `lake build JinWishartFormalization --quiet` 退出码 0。
- 下一步：推广任意复均值方向，再提交独立审查。一般维数、多
  特征值 Theorem 1–4 仍属于 G1–G4，绝不能将此轴向特例记作全文形式化。

### 执行状态补记（2026-09-27，任意均值方向桥接）

- `NoncentralFourDimensionalGaussianCDF.lean` 新增并通过构建：四维标准高斯在任意
  非零平移下的闭球概率只依赖平移向量的范数，并等于相应的 Nuttall-
  `Q_{2,1}` 尾概率表达式。
- `TwoRowSampleCoordinates.lean` 新增坐标恒等式：对任意 `2×1` 复均值矩阵 `M`，
  实高斯编码均值满足 `‖complexSampleMean M‖² / 2 = ∑ i, ‖M i 0‖²`，并通过
  Lean 构建。这核对了论文一列情形的非中心参数与平方 Frobenius 范数。
- `Theorem1TwoRowsActualCDF.lean` 因而已证明：非零任意复均值方向下，论文 T1 与
  T2 的 `(s,t,L)=(1,2,1)` 候选式均等于实际单列 Wishart 唯一特征值的 CDF；候选式
  中 `λ=‖complexSampleMean M‖²/2`。此处沿用现有标准复高斯样本空间及方差约定。
- 同一文件新增明确的唯一 Gram 特征值统计量，并将 T2 的结果另行表述为最大（唯一）
  Gram 特征值的 CDF，避免仅依赖 `s=1` 时最大/最小相同这一隐含说明。
- `TwoRowSmallOutageAsymptotic.lean` 已证明中心与任意非中心 `2×1` 模型的统一实际
  CDF 极限：`F(x)/x² → (1/2) exp(-‖complexSampleMean M‖²/2)`，包括零均值边界。
- 独立只读数学审查确认了本轮复高斯尺度、非中心参数换算、半径和 T1/T2 特例公式；
  并指出了论文非中心矩阵谱参数的形式语义缺口。新文件
  `TwoRowMeanGramSpectrum.lean` 已补证 `2×1` 均值 Gram 矩阵的唯一特征值等于
  `∑ i ‖M i 0‖² = ‖complexSampleMean M‖²/2`。极坐标、球面参数化、Fubini/换元和
  相关可积性仍须人工测度审查。
- 另一模型家族完成了 P4 对抗复核：未发现本轮 Lean 新增占位符或尺度错误；特别要求
  对四维球面测度归一化、chart 边界/重数、去除原点零测集以及 Fubini/换元常数保留
  `[需人工审查]`。同时确认当前定理仅为单列 4 实维模型，不能外推到一般有序谱或全文。
- 新增模块和 `OrderedEigenvalueWeyl.lean` 均已接入 facade；本轮
  `lake build JinWishartFormalization --quiet` 退出码 0。以上仍只覆盖 `2×1` 特例，
  一般维数和多个有序特征值尚未覆盖。
- G1 新文件 `OrderedEigenvalueWeyl.lean` 已证明点态 Rayleigh 商扰动界以及特征
  向量上的 Rayleigh 商等于相应特征值；`SubspaceIntersectionFinrank.lean` 现已证明
  `finrank U + finrank V > finrank E` 时子空间交非零；`IndexedCourantFischerAttempt.lean`
  证明了基向量子集张成空间的维数等于其指标数。Rayleigh 商在 head/tail 特征子空间
  上的有限加权平均估计已独立证明；`SpectralRayleighCoordinates.lean` 进一步证明实
  内积有限维对称算子中，谱坐标在 i 之前均为零时 Rayleigh 商 `≤ λ_i`。前缀反向界、
  完整实对称 Courant–Fischer 桥接和逐指标 Weyl 界现均已证明（见后续记录）；但从
  复 Hermitian Gram 矩阵到此实定理的桥接、一般复矩阵中间有序特征值的可测性仍缺失。

### `PaperStatements.lean` 的原文对齐审计（2026-09-27，独立 P4）

该文件只能作为陈述层草案，不能作为原论文定理已被准确形式化或完成的证据。对照
[官方 arXiv v2](https://arxiv.org/pdf/cs/0611007)（定理 1–4 为式 (15)–(34)，性能
部分为式 (35)–(45)）发现：

- T1/T2 契约未连接实际 Wishart 概率模型，没有 probability-measure、`x>0`、非中心谱
  参数正性/互异/来自 Ω 等条件，也未限制任意抽象 law 与候选公式必须匹配。
- T3 只要求存在函数 `F`，并在单点匹配 k、1、s 三个值；没有原文 (22) 的递推，也没有
  (23)–(25) 的概率项、常数、组合求和或 Θ/Ψ/Ξ 行列式结构，属于过弱占位契约。
- T4 只表达某正系数下的 CDF 幂次极限，缺少 PDF 一阶展开、CDF 系数的显式公式，以及
  原文 (31)–(34) 的矩阵/非中心谱参数定义。新证的 `2×1` 极限是实际模型特例，不是一般 T4。
- SER/outage 契约没有表达原文 (35)–(45) 的 Q 核、调制常数、SNR/功率缩放、per-mode 与
  global 关系或低 outage 渐近。`OutageClaim` 允许 scale·power=0，却把 RHS 写成除以该乘积；
  现有缩放证明只有额外假设乘积非零时才正确。
- 抽象 `OrderedEigenvalueLaw` 缺 probability-measure 与 Wishart-law 连接；其 `strictAnti`
  要求每个样本点严格谱序，强于简单谱几乎处处成立并排除了退化零测点。

所以后续一般 T1–T4/性能工作必须先修订这些契约，使 Lean 的模型、参数域和公式逐项对应
原文；算术恒等式或存在性定义不得记作论文定理完成。

## 7. 一般维度长线任务卡（不可用特例冒充）

这部分数学和形式化工作量都大。轻量模型应逐张卡做定义/局部引理，遇到缺失的深层定理时交给强模型，不应靠改写结论绕开。

### G1 ✅（谱可测范围）— 论文小侧 Gram 及整组有序谱可测已完成；谱联合密度仍属 G2

- 明确矩阵尺寸、秩、协方差正定性、非中心参数、谱排序和退化谱处理。
- 已证明所有排序坐标在 Hermitian 矩阵上 Lipschitz 连续；`PaperSmallSideGram.lean` 已把 `XXᴴ`/`XᴴX` 按长宽 reindex 到 `Fin (min m n)`，证明实际 shifted Gaussian 小侧 Gram 与 PSD 子型可测；facade 的 `measurable_paperSmallSideSampleEigenvalueVector` 再给出论文对应的整组有序谱可测性。G1 的谱可测范围完成。两种 Gram 非零谱对应仍可作为独立谱代数结果补充，但不是当前小侧模型可测性的前提；重根零测和联合密度仍属 G2。
- 验收：一般维度随机特征值向量是真正的可测映射，定义域与实际复高斯 Gram 模型一致；主 facade 全构建通过。

### G2 — 联合特征值分布

- 确认论文所用的非中心复 Wishart 联合密度、矩阵超几何/Bessel/行列式表达式、Vandermonde 与正规化常数的确切条件。先研究 Mathlib 现有矩阵积分与特殊函数资产；缺失的结构写为最小局部引理，不伪装已有库支持。
- 证明从矩阵高斯密度到联合特征值密度的测度变换，包含 Jacobian、酉群积分、重根零测集及常数核验；每一项标 `[需人工审查]`。
- 验收：联合密度左边仍是实际矩阵模型的推前测度，不仅是手写的候选密度；积分为 1；独立审稿通过。没有这张卡，不得宣称一般定理 1/2 已完成。

### G3 — 论文其余特征值公式/定理 3

- 在 G2 之后证明论文所用的行列式积分/Andreief 型公式及边界条件，再得到一般维度 CDF、极值或联合公式。每个公式先证明积分恒等式，再连接随机事件；检查矩阵维度、行列顺序、符号和退化参数。
- 验收：定理追踪表中的原文陈述与 Lean theorem 双向核对；非中心与中心特例数值 sanity check；主工程构建和独立审查通过。

### G4 — 定理 4、outage/SER 与全文封闭

- 精确区分论文中的 outage/SER、硬边渐近、通信系统的 SNR 缩放与单纯标量缩放。`1×1` 已有的 hard-edge/弱 outage 结果不能自动推广。证明所需极限、支配界、积分交换和误码率映射，逐项审查。
- 验收：定理 1–4（及论文主张的推论）每一条都具有“原文—Lean—模型桥—审查”证据链；无未解释的 `[待核实]`；运行所有 Lean/Python 检查；在 README 明确论文版本和超出/未覆盖的范围。

## 8. 全程记录、验证和交接卡

### R1 — 每次完成后更新台账

- 更新 `notes/JIN_WISHART_THEOREM_TRACKER.md` 和相关 README：仅写经构建证明的能力，分开记录公式侧、候选密度、真实概率律、论文定理。引用不确定时标 `[待核实]`。外部 Wishart 库的版本/许可证差异先审查；不能为节省时间直接复制 GPL 代码进入本仓库。
- 最小验证：Python 改动运行 `D:\miniconda3\python.exe -m unittest discover -s tests -v`；Lean 改动先运行目标模块构建，再运行 `& 'D:\vibe math\.tools\elan\bin\lake.exe' build JinWishartFormalization --quiet`。另用文本搜索审查新 `sorry`、`admit`、`axiom`，但文本搜索不能代替类型与语义审查。
- 完成一次“可运行状态”后只暂存本卡文件并提交。提交说明必须区分“基础设施/特殊情形/一般定理”，不能使用笼统的“complete formalization”。

### 交接模板（每张卡结束时填写）

```text
任务卡 ID：
改动文件：
数学陈述（含全部参数域）：
本次真正证明了什么；没有证明什么：
验证命令、退出码和关键输出：
新增的测度论/数值/文献待审项：
Git 提交哈希（如未提交，原因）：
下一张卡及阻碍：
```

## 9. 给轻量执行 AI 的可复制首轮指令

```text
你在 D:\vibe math 仓库工作。先完整阅读 AGENTS.md 和
notes/JIN_WISHART_EXECUTION_PLAN.md。本轮只执行 B0，禁止顺手修改 Python
或 Lean 证明。先运行 git status --short，保留一切既有未提交文件；核对论文
原文、notes/jin_2006_wishart_summary.md、Lean README 与主入口，建立
notes/JIN_WISHART_THEOREM_TRACKER.md。每个定理写原文假设、模型、结论、
现有 Lean theorem、真实完成状态和缺口。无法核实的原文信息标 [待核实]，
不得猜测。只用 apply_patch 编辑文件；只暂存并提交本轮新建的追踪表。
结束时按本计划第 8 节的交接模板报告，特别说明哪些 theorem 仅证明公式侧。
```

后续轮次只把“本轮只执行 B0”替换为一张已满足前置条件的卡片编号，并附上上轮交接。若后续使用更强模型，优先交给它审查 M1/M2、G2 及所有 `[需人工审查]` 项，而不是让它重复机械的语法修补。

### 2026-09-27 继续推进记录

- 新增 `TwoRowOutageScaling.lean` 并接入 facade。它证明实际 `2×1` shifted complex Gaussian Gram 最小特征值的正尺度弱 outage CDF 恒等式，并把已证小阈值二阶极限搬运到高 scale：
  `scale² · P(scale·φ_min ≤ γ) → γ²/2 · exp(-‖complexSampleMean M‖²/2)`（任意均值，含中心情形）。目标模块编译通过；没有声称这就是论文 (42)–(44)，因为仍未把 scale、均值映射到 `ε²P/r`、`K` 与 `H̄`。
- G1 新增 `SpectralCoordinateSpanSupport.lean`：证明谱基向量张成空间成员在补集坐标为零，并据此得到 prefix/tail 子空间上的 Rayleigh 商界。经 Finset image 维数桥接后，`IndexedCourantFischerProof.lean` 的完整实对称 indexed min–max 已目标编译通过并接入 facade。
- `WeylRealSymmetric.lean` 再证明有限维实内积空间中，对称连续线性算子的每个有序特征值满足 `|λᵢ(T)-λᵢ(S)| ≤ ‖T-S‖`；使用谱头/尾交空间和 Rayleigh 扰动界，目标编译通过并接入 facade。它尚未处理复 Hermitian 表示桥接或 Wishart 随机变量可测性。
- 验证：集成 `TwoRowOutageScaling`、indexed min–max 与实对称 Weyl 模块后的全 facade `lake build JinWishartFormalization --quiet` 退出码 0。新增谱论/两行 outage 模块文本审查无 `sorry`、`admit` 或新增 `axiom`。极坐标、球面推前、Fubini/换元等人工测度审查边界不变。
- 入口集成后的二次验证：`lake build JinWishartFormalization --quiet` 退出码 0，确认 `TwoRowOutageScaling` 已纳入 facade 且全库仍可编译。
- G1 新增正式谱定理：`IndexedCourantFischerProof.indexedCourantFischerValue_eq_eigenvalue` 给出有限维实内积空间上的连续实对称算子 min–max 表征；`WeylRealSymmetric.abs_eigenvalue_sub_le_operatorNorm` 及 `WeylComplexHermitian.abs_eigenvalue_sub_le_operatorNorm_rclike` 给出逐指标 Weyl 界，后者适用于 RCLike 上的实/复内积空间。复 Weyl 界进一步给出 Hermitian 有序特征值坐标 Lipschitz 连续性，主 facade 的 `measurable_complexNoncentralSampleEigenvalueVector` 闭合仓库 `XᴴX` 全谱可测性；论文小侧 `s=min(m,n)` Gram 及非零谱对应仍待完成，G1 也不包含重根零测或联合密度。
- 论文物理参数闭合一个实际边界：`PaperSingleStreamTwoRowOutage.lean` 将 (2)、(12)–(14)、(42)–(44) 实例化到 `s=1,t=2,r=1`，证明 `ε²P=P/(K+1)`、标准化均值为 `√K H̄`；若 `‖H̄‖F²=2`，则非中心参数为 `2K`，且 `P²Pout → (K+1)²γ_th²e^{-2K}/2`。这是论文结论的真实 `2×1` 单流特例，不是一般 MRC/一般 outage 定理；接入 facade 后全量构建退出码 0。
- facade 现另证明该 `2×1` 单流 outage 主系数在 `K>0` 上严格递减（`paperTwoRowOutageCoefficient_strictAntiOn`），即式 (45) 的该特例。包含复 RCLike Weyl、条件全谱可测性、物理参数 outage 和系数单调性的新 facade 构建通过，退出码 0。
- `WeylComplexHermitian.lean` 现以复 Weyl 界证明所有 Hermitian 有序特征值坐标 Lipschitz 连续，并在 facade 合成得到实际随机 Gram 全谱可测性。此前一次直接 ε-δ 写法曾因 subtype 拓扑实例不匹配而失败并已撤回；最终采用 `SymmetricCLM` 子类型上的 Weyl-Lipschitz 映射与连续复合方案，验证通过。
- 论文物理参数又闭合一个实际边界：`PaperSingleStreamTwoRowOutage.lean` 将 (2)、(12)–(14)、(42)–(44) 精确实例化到 `s=1,t=2,r=1`，证明 `ε²P=P/(K+1)`、标准化均值为 `√K H̄`；若 `‖H̄‖F²=2`，则非中心参数是 `2K`，并证明 `P²Pout → (K+1)²γ_th²e^{-2K}/2`。这是论文结论的真实 `2×1` 单流特例，不是一般 MRC/一般 outage 定理；当前刚接入 facade，待全量构建复验。
- 继续推进：`PaperStatements.lean` 的 `OrderedEigenvalueLaw.kth` 曾将 1-based 第 k 大错映到索引 `s-k`（第 k 小）；现已改成 `k-1`，加入 `k=1` 对最大、`k=s` 对最小的编译证明，并给最大值/Theorem 2 契约补上必要的 `s>0`。新增 `orderedEigenvalueLaw_kthCDFRecurrence_strict`，按论文索引证明 (22) 的事件递推（明确给阈值零原子假设）。目标模块已构建通过，接入后的 facade 3295 jobs 构建通过。
- 继续推进 T3：`DeterminantRowExpansion.lean` 新增并单独构建通过任意有限维交换环上的 Leibniz 行展开 `det(A+B)=∑_{S⊆univ} det(rowMix(A,B,S))`。它是行混合的代数基础设施；论文 (23) 只对固定 `|S|=k-1` 求和，故尚需适配固定基数并证明 Wishart 有序区域积分/概率恒等式。该模块已加入 facade，构建通过。
- 继续推进 T4：新增 `T4CentralOneColumnAnyRows.lean`，对任意正整数 `m` 从实际中心 `m×1` 复高斯 Gram/Gamma 法则证明 `F(x)/x^m → 1/m!`。此为中心单列的真实模型推广，模块及集成该模块后的 facade（3296 jobs）均构建通过；一般 `s>1` 与非中心多秩的谱相互作用和渐近积分仍未解决。
- 历史状态校准（已在下条解决谱可测缺口）：复核论文 `s=min(m,n)` 后发现此前的 `measurable_complexNoncentralSampleEigenvalueVector` 仅给仓库 `XᴴX`（`n×n`）谱，不能直接充当论文小侧桥；后新增的 `PaperSmallSideGram` 与 facade 定理已解决小侧谱可测性。此前将 G1 暂降级的记录保留为审计轨迹；Theorem 1–4 全文仍未完成。
- 继续推进 T4：`T4DensityToCDF.lean : density_to_cdf_hardEdge` 对任意自然数 `d` 证明一般解析桥：若 `f(u)=u^d g(u)`、`g(u)→a` 且每个正小区间上 `f` 可积，则 `x^{-(d+1)}∫₀ˣf(u)du→a/(d+1)`。独立模块构建和接入后的 facade（3298 jobs, `--quiet`）均通过。它不提供 Wishart 密度首项本身。
- G2 审查补充：`RepeatedRootNullSets.lean` 已独立证明一元非零实多项式零点集的 Lebesgue 零测及绝对连续测度推论，并接入 facade；这尚未推广到多元判别式、证明判别式非零或连接复高斯矩阵系数，不能算 Wishart 谱简根结论。独立模块构建与之后的全 facade 构建均通过。
- 继续推进 t=3 单列分析：`SixDimensionalAngularBesselI2.lean` 证明六维球 S⁵ 轴向角积分的精确 I₂ 幂级数：`∫_{-1}^1 exp(a u)(1-u²)^(3/2)du = (3π/4)∑ (a²/4)^j/(j!(j+2)!)`，并形式化 `u=cos θ` 换元。随后 `SphereSixDAxialMeasure.lean` 证明实际 `toSphere` 测度的指数核积分等于 `(8π²/3)∫₀^π sin⁴(θ)exp(κ cos θ)dθ`，并核对 S⁵ 总质量 `π³`；模块已接入 facade，总构建 3303 jobs 通过。该结果只针对指数核，仍未闭合实际非中心 CDF 的 Nuttall-Q 桥。
- G1 小侧谱桥闭合：`PaperSmallSideGram.lean` 直接在 `Fin (min m n)` 上定义按长宽选择的 Gram，证明其 PSD 及在真实 shifted complex-Gaussian 坐标下的矩阵可测性；facade 新定理 `measurable_paperSmallSideSampleEigenvalueVector` 使用既有有序 Hermitian 特征值连续性，证明论文 dimension `s=min(m,n)` 上完整谱向量可测。模块目标构建通过，集成该模块与 T3 后的 facade 构建通过（3301 jobs）。它不证明联合密度、谱简根或 Theorem 1–4 的 CDF 公式等式。
- 继续推进 T3：`T3FixedCardinalityRowSelection.lean : coeff_det_rowAffinePolynomial_eq_fixedCardRowSum` 已独立构建通过，并接入 facade；集成小侧谱桥与该模块后的总入口构建通过（3301 jobs）。对任意有限指标集与交换环，证明 `det(B+X A)` 的 `X^p` 系数是从 `A` 选恰好 `p` 行、补集从 `B` 选行所得行混合行列式之和；通过对角行选择矩阵证明各项次数。它只闭合固定基数行选择代数，不含论文 Ψ/Ξ 具体块、概率常数或实际 CDF 积分。
- T3 进一步对齐论文原文：新 `T3PaperThetaSpecialization.lean` 定义 Theorem 3 的 `c₃`、按组合索引行选的 `Θ_S` 和固定基数和，并证明该和等于 `det(Ξ+zΨ)` 的指定多项式系数。原文编号为 (23)–(26),(48)，官方 HTML 对照来源为 [arXiv:cs/0611007](https://arxiv.org/html/cs/0611007)。初版把 (25) 中 `Γ_{s-L}(s-L)` 错放在分子；本轮已核实并移至分母，修正后的总 facade 构建通过（3305 jobs）。此代数结果仍未把候选值连到概率 `p`。
- T3 对 Appendix III 的分层审计：论文从有序特征值联合密度与 Vandermonde/行列式展开出发，按阈值上下变量分组，拆成一维尾/下尾积分并识别为 Ψ/Ξ 条目，最后提出行列式共因子把 `c₁` 化成 `c₃`。当前行混合的自然行顺序与原文 `Θ_{α_i,j}` 的索引一致；不需额外 shuffle 符号。尚缺的实质证明：Wishart 联合谱密度（矩阵谱 Jacobian、任意秩极限）、有序域置换对称化与 Fubini/绝对可积性、一般 `0F1` 核与 Nuttall-Q 的一维换元/可积性、`c₁→c₃` 因子化，以及候选复嵌入矩阵的实值性。参见 [论文 Appendix III](https://arxiv.org/pdf/cs/0611007)。
- T3 常数对抗审计：按 Appendix A 的 `c₁` 与 Appendix III 的列积分缩放（arXiv HTML Eq. 64–66；PDF 编号对应关系待核）逐列抽因子，得到 `c₁∏d_j = c₃ / Γ_{s-L}(t-L)`，而非显示的 `c₃`；例如 `s=3,t=4,L=1` 留下因子 `1/2`。arXiv HTML Eq. 25 的 `c₃` 确为 `Γ_{s-L}(s-L)` 分母；HTML Eq. 60 实为导数式，旧笔记的 Eq. 60 列缩放引用已更正。尚不能判断是原文归一化遗漏还是 Appendix III 省略了未显示的变换；完整概率等式在核实前继续保持未形式化。详细算式见 `notes/T3_C1_C3_normalization_audit.md`。
- G2 通用多项式工具扩展：`MvPolynomialZeroSetNull.lean : mvPolynomial_zeroSet_volume_eq_zero` 独立构建通过（2641 jobs），随后已接入 facade；修正 T3 常数后的完整入口构建通过（3305 jobs）。该定理只说明非零实多项式的有限维 Lebesgue 零集性质，尚未应用到 Gram 判别式，也未证明其非零或桥接 shifted Gaussian。
- 继续推进 `t=3` 单列非中心路线：`NoncentralSixDimensionalRadial.lean` 构建通过，证明轴向非中心六维实高斯球壳在真实 S⁵ `toSphere` 测度下等于显式 I₂ 阶乘级数核，并连接到 `nuttallQIntegrand 3 2 / a²`。随后 `ThreeRowSampleCoordinates.lean` 证明复 `3×1` 样本坐标等距、任意均值的 E₆ 正交旋转/球事件映射，以及任意复均值下实际最小 Gram 特征值弱 CDF 等于有限半径级数积分 `∫_(0,√(2x)] kernel`。两个模块单独构建和接入后的 facade（3312 jobs）均通过。仍缺 Nuttall-Q 尾质量归一化和任意 `3×n` 谱结论。
- 再推进 `t=3` 径向核：`NoncentralSixDimensionalRadial.lean` 新增并独立构建通过 K₆ 的非负性、可测性，以及中心参数 `a=0` 时 `∫_(0,∞)K₆=1` 的闭式证明（`r⁵e^{-r²/2}` 六阶径向积分）。任意 `a≠0` 的总质量→Nuttall-Q 尾归一化还在尝试接概率 CDF 极限与 MCT；新增声明尚待 facade 总构建复验。
- T3 常数复核（PDF/HTML 编号已逐式核对）：PDF Theorem 3 Eq. (24) / HTML Eq. (25) 的 `c₃` 分母只有 `Γ_{s-L}(s-L)`；PDF Appendix I Eq. (60) 的列积分对应 HTML Eq. (66)，Appendix III PDF Eqs. (65)–(69) 对应 HTML Eqs. (72)–(76)。由 PDF Eq. (47) 的 `c₁` 与 Eq. (60) 逐列抽因子，仍精确多出 `Γ_{s-L}(t-L)`；PDF Eq. (54) 才是导数值公式。`s=3,t=4,L=1` 留下 `1/2`，百万次模拟仅作诊断。原文展示的公式存在代数归一化不一致，但尚不足以判定实际概率定理错误；细节见 `notes/T3_C1_C3_normalization_audit.md`。
- 最新并行轮（2026-09-27）：`T3NormalizationAudit.lean` 独立构建通过，机检主恒等式 `paperC1_mul_columnFactors_eq_paperC3_div_inactiveGamma`，精确显示附录 A 列因子乘积与 Theorem 3 `c₃` 尚差 `Γ_{s-L}(t-L)`；这加强了代数审计，但不等于概率公式反例或证明。
- 最新并行轮：`NoncentralSixDimensionalRadial.lean` 与 `NoncentralSixDimensionalMass.lean` 分别通过独立构建；对所有实振幅 `a`，六维径向级数核非负、可测、正半轴可积且积分等于 1。`NoncentralThreeRowNuttallQ.lean` 通过，给出任意复均值 `3×1` 最小 Gram 特征值 CDF 的归一化 `Q_{3,2}` 实部尾积分表示。
- 最新并行轮：`Theorem1ThreeRowsActualCDF.lean` 独立构建通过，证明 `(s,t,L)=(1,3,1)`、`λ>0,x≥0` 且 `‖encodedMean‖²=2λ` 下论文 Theorem 1 候选等于真实复 `3×1` shifted Gaussian Gram 最小特征值 CDF；现已从轴向均值推广至任意复均值方向，但不是一般行列维数结论。
- 最新并行轮：`Theorem2ThreeRowsActualCDF.lean` 单目标构建通过，证明同一 `(1,3,1)` 单列非中心特例下、任意均值方向且参数满足 `‖encodedMean‖²=2λ` 时，Theorem 2 候选等于真实 CDF；单列 Gram 的唯一特征值同时是最大与最小特征值。
- 最新并行轮：`MvPolynomialGramTwoByTwo.lean` 实 `2×2` Gram 判别式零集结果（2744 jobs）、`RealQuadraticRepeatedRoot.lean` 重根判别式桥（1540 jobs）和 `ComplexGramTwoByTwoDiscriminantNull.lean` 复 `2×2` 八实坐标判别式零测模块（2744 jobs）均独立构建通过；均未连接 Gaussian 绝对连续律或一般维数 Wishart。
- 最新总入口回归：新增的 T3 常数审计、六维径向质量与 Nuttall-Q CDF、Theorem 1/2 的 `3×1` 非中心单列特例、实/复 `2×2` Gram 多项式零测及二次重根判别式引理均已接入 `JinWishartFormalization.lean`；`lake build JinWishartFormalization --quiet` 通过（3321 jobs）。`sorry/admit/axiom` 扫描无命中；`git diff --check` 无空白错误（仅有 Git 行尾转换提示）。这仍不是全文形式化，主表中的一般联合谱密度/多列概率等式、T3 概率桥和 T4 一般渐近仍缺失。

### 2026-09-28 继续推进记录（Claude Code 会话）

- 修复三个编译失败的叶子模块（证明内容与陈述不变）：`Theorem12ThreeRowsFrobeniusCDF`（参数类型 `Ioi`→`0≤r`、冗余 `ring`）、`FinSpectralIndexCard`（`simpa` 化简为 `True`，改为显式 `Finset.Iic/Ici` 计数）、`MIMOWishartSERExact`（过时 tactic、未知常量 `Real.measurable_sqrt.comp`、前向引用；重写证明骨架）。
- 将 `ComplexGramTwoByTwoGaussianSimpleSpectrum`、`Theorem12ThreeRowsFrobeniusCDF`、`FinSpectralIndexCard`、`MIMOWishartSERExact`、`PaperStatements` 接入 facade；`lean_import_graph.py` 现报告叶子模块为 (none)。
- G2 新增 `ComplexGramSimpleSpectrum.lean`：复系数多元多项式实零点零测（任意有限指标）；通用复样本 Gram 的 charpoly/导数 resultant 及其求值桥；resultant 非零 ⟹ Hermitian 有序特征值单射；对角见证均值证明 resultant 非零（`XᴴX` 需 `n≤m`，`XXᴴ` 需 `m≤n`）；主定理 `paperSmallSideGram_eigenvalues_strictAnti_ae`：任意 `m×n`、任意复均值下论文小侧 Gram 有序谱几乎必然严格递减。`#print axioms` 仅标准三公理。
- 验证：`lake build JinWishartFormalization` 退出码 0（3328 jobs）；`sorry/admit/axiom/native_decide` 扫描无命中。首次全量构建曾因 mathlib 缓存 `Finsupp/Basic.olean.private` 读取失败（Windows 偶发），原样重跑通过。
- `[需人工审查]`：Gaussian 绝对连续与平移的测度论链复用既有 `stdGaussian_euclidean_eq_radialDensity`；新模块未引入新的 Fubini/换元。
- 下一步建议：同一 resultant 路线证明阈值无原子 `P(φ_k = x) = 0`（对 `det(G - xI)` 作为样本坐标多项式，非零性用缩放见证），从而把 `orderedEigenvalueLaw_kthCDFRecurrence_strict` 的无原子假设在真实模型上消去。

### 2026-09-28 继续推进记录（Codex）

- `Theorem12ThreeRowsFrobeniusCDF.lean` 通过单目标构建；任意复均值 `3×1` 下，T1/T2 的 `(s,t,L)=(1,3,1)` 实际 CDF 等式现在直接使用论文非中心参数 `λ=∑ᵢ‖Mᵢ₀‖²`，借助 `ThreeRowMeanNorm.lean` 的精确范数桥。T2 的归约用到了 Q 尾积分核非负、总质量 1 及尾集包含关系；独立静态审查未发现逻辑跳步。随后主 facade 构建通过（3331 jobs）。
- `ComplexGramTwoByTwoGaussianSimpleSpectrum.lean` 经独立审查和单目标构建通过：对任意确定复均值的 `2×2` shifted complex Gaussian 样本，其 Gram 判别式为零的概率是 0；仅属 2×2 简谱结论。
- `T4CentralOneColumnHighScale.lean` 将中心 `m×1` 实际小阈值硬边极限转成固定正阈值的高尺度 outage 渐近 `scale^m·P(scale·λ_min≤γ)→γ^m/m!`（`m>0,γ>0`）；单目标构建通过并已接入主 facade。
- `EightDimensionalAngularBesselI3.lean` 单目标构建通过，证明 `∫₀^π sin⁶(θ)e^{a cos θ}dθ` 的阶乘级数表达，等价于分母无关形式 `a³ I(a)=15π·besselI3RealSeries(a)`；偶/奇矩、Taylor 级数换序经独立数学审查。该文件不证明真实 `S⁷` 球面测度的角坐标推前，也未识别 Mathlib 的 `modifiedBesselI 3`。
- `T3InactiveColumnCancellation.lean` 单目标构建通过，给出残余多元阶乘何时能在 `c₁×columnFactors=c₃` 中纯代数抵消的 iff，并证明正互异活跃参数时 `c₃≠0`；`(s,t,L)=(3,4,1)` 的残余因子为 2。它仍不证明 Appendix C 的置换/矩阵归一化或 T3 概率公式。
- `RectangularGramEigenvectorBridge.lean` 单目标构建通过，给出矩形 `BA` 与 `AB` 非零特征值特征向量之间由矩阵作用显式传递的桥；现有 `GramSpectrumTransfer` 已更强地覆盖代数重数，因此此模块补充向量映射，不是新的概率结论。
- `SphereEightDAxialMeasure.lean` 单目标构建通过，核验 S⁷、横向 S⁶ 的球面总质量与候选 `sin⁶` 角密度归一化常数；模块不含 S⁷ 角坐标 pushforward。
- 新增待验纯代数模块 `T3PermutationCoefficientBridge.lean`，将固定行选择系数恒等式显式展开为 Leibniz 置换和；静态审查认为定义与索引一致，但该结论不提供 T3 所缺的概率积分桥，尚未编译、尚未纳入主入口。
- 新增上述模块、`SphereEightDAxialMeasure` 和 `RectangularGramEigenvectorBridge` 后，主入口回归构建退出码 0（3336 jobs）。本轮已编译新增 Lean 文件无 `sorry`、`admit`、`axiom` 命中。
- `NoncentralEvenDimensionalPoissonMixture.lean` 点态 Poisson 混合恒等式及四维/六维特例已单目标编译通过，现接入 facade；证明的是径向级数核恒等式，不是实际 shifted Gaussian 的 CDF。
- `T3CentralTwoByTwoDensityInterface.lean` 单目标编译通过，现接入 facade。它把实际中心 `2×2` T3 事件概率化成候选密度积分，但前提 `hDensity` 尚未证明，不计作 T3 概率公式完成。
- 并行审查确认 T3 密度桥当前的首要缺口不是术语/API，而是两项数学结果：复 `2×2` Gram 矩阵的 Lebesgue 密度，以及 Hermitian 矩阵到有序特征值/角变量的 Jacobian 换元与归一化。
- 一般行数单列 Frobenius 参数转换新引理正在修复第一次编译报错；它是参数基础设施，不能增加实际 CDF 定理覆盖率。
- `OneColumnFrobeniusParameter.lean` 现已单目标编译通过并接入 facade；对任意行数统一给出单列均值编码的 Frobenius 参数转换，仍不单独扩展已闭合的概率 CDF 特例。
- 上述三个新增模块接入后，`lake build JinWishartFormalization --quiet` 通过（3339 jobs）；三个文件均无 `sorry`、`admit` 或正式 `axiom` 声明。`git diff --check` 通过（仅提示既有文件的 LF/CRLF 转换）。
- `notes/THEOREM_COVERAGE_AUDIT.md` 新增独立覆盖审计，逐项区分实际模型闭环、公式侧/抽象接口与未覆盖主定理；它指出 T3 Γ 因子源文裁决应先于继续写概率桥。
- 本轮核对后，整体仍未完成：一般维数/多列联合特征值密度和 Theorem 1–2 概率等式、T3 的概率桥与归一化源文审计、一般非中心多列 T4/SER/outage 结论仍是主缺口。
