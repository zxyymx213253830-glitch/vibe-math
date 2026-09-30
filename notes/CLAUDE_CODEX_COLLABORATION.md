# Claude ↔ Codex 协作协议（Lean 部分）

建立：2026-09-28，Claude Code 会话起草，待用户确认。
Codex 侧模型：**GPT-6 Luna**（调用时显式 `-m gpt-6-luna`；本机 `~/.codex/config.toml`
默认是 `gpt-5.6-sol`，不显式指定会用错模型）。

## 1. 通信通道（已实测）

- **可用**：Claude 在自己的 PowerShell 中用 Codex CLI 驱动 Codex：
  - 新开：`codex exec -m gpt-6-luna "<消息>" -C "D:\vibe math" -s <沙箱> -o .codex_bridge_reply.txt --json`
  - 续接同一会话（保留上下文）：`codex exec resume <SESSION_ID> "<下一条>"`
- **不可用**：用户在另一个终端里交互运行的 Codex 会话，Claude 连不上。`codex agents` /
  `app-server daemon` 的共享控制 socket 在本机报 `os error 10050`（Windows 上未就绪）。
  Codex 桌面版自身的 app-server 进程在跑，但不对 CLI 开放。
- 用户可在任意时刻用 `codex resume <SESSION_ID>` 打开同一会话旁观（避免与 Claude 同时发消息，以免分叉）。

## 2. 分工（按证明方向切，不按文件抢）

| 角色 | 方向 | 拥有文件 | 沙箱 |
|---|---|---|---|
| **Claude**（协调者 + G2 主线） | G2：谱简根（✅）、阈值无原子、联合谱密度规划；facade 集成、全量构建、台账中 Lean 行 | `ComplexGramSimpleSpectrum.lean`、新 `ThresholdNoAtom.lean` 及后续 G2 模块；`JinWishartFormalization.lean`（facade） | 本会话 |
| **Codex / GPT-6 Luna**（解析主线 + 审稿） | 特殊函数与单列解析：任意 t 单列统一（一般 `S^{2t-1}`）、Nuttall `Q_{t,t-1}` 归一化；T3 常数审计；T4 首项；**对 Claude 的每个定理做 P4 审查** | Nuttall*/Bessel*/Sphere*/Noncentral*/Theorem1*/Theorem2*/T3*/T4* 及其新模块 | 审查用 `read-only`；写证明用 `workspace-write`，只写自己的文件 |
| **step5preview** | Python、数值对照、提交 | `infoq/**`、`tests/**`、`experiments/`、`verification/`、`notes/AGENT_DIVISION_OF_LABOUR.md` | — |

## 3. 硬规则

1. **构建单出口**：只有 Claude 跑 `lake build` 和改 facade。Codex 只用
   `lake env lean <file>` 单文件检查，写完在第 5 节登记，由 Claude 接入。
2. **提交单出口**：只有 step5preview 执行 git；Claude 在第 5 节写 `READY TO COMMIT` + 文件清单。
3. **交叉审查**：Claude 的定理由 Codex 审，Codex 的定理由 Claude 审（P4，模型家族不同）。
   审查只报告问题，不改对方文件。
4. **无占位**：禁止 `sorry/admit/axiom/native_decide`；每个新主定理附 `#print axioms` 结果。
5. **测度论步骤**标 `[需人工审查]`，不因 Lean 通过而删除。

## 4. 一轮协作的节拍

```text
Claude 派卡 (codex exec, workspace-write, 限定文件)
  -> Codex 单文件编译通过, 回报 模块名/主定理/axioms
  -> Claude 审陈述 (P4) + 接入 facade + 全量 lake build
  -> Codex 审 Claude 同期产出 (read-only)
  -> step5preview 数值对照 + 台账 + git 提交
```

## 5. 交接登记区（只追加）

- 2026-09-28 Claude：`ComplexGramSimpleSpectrum.lean` 已接入 facade，全量构建 3328 jobs 通过；待 Codex P4 审查。
- 2026-09-28 Claude：**G2b 完成** `ThresholdNoAtom.lean`（已接入 facade，全量构建 3329 jobs，axioms 仅标准三项）：
  - `paperSmallSideGram_eigenvalues_ne_threshold_ae`：任意 `m×n`、任意复均值、任意固定 `x`，小侧 Gram 无特征值等于 `x`（a.s.）；
  - `paperModelLaw`：真实 shifted Gaussian 模型实例化 `Paper.OrderedEigenvalueLaw`（可测/有序/a.s. 严格/非负四字段全证）；
  - `paperModel_kthCDFRecurrence_strict`：论文式 (22) 在真实模型上**无条件**成立（原无原子假设已消去）。
  - 附带：`ComplexGramSimpleSpectrum` 的 `sampleEval_ne_zero_ae`、`charpoly_submatrix_equiv` 由 private 改为公开（供复用）。
- 2026-09-28 Claude → **step5preview 数值对照请求**（固定种子，与 Lean 陈述对齐）：
  1. 取 `(m,n)∈{(3,3),(3,5),(4,2)}`、非零复均值、`N=10⁶`：统计有序小侧 Gram 特征值最小间隙 `min_k(φ_k−φ_{k+1})` 的经验分布，确认无零间隙（对应 `strictAnti_ae`）；
  2. 同设定、若干固定 `x`：核对 `P(φ_k≤x) = P(φ_{k−1}≤x) + P(φ_k<x<φ_{k−1})`（式 (22)），两侧经验值差应在 MC 误差内；
  3. 注意 Lean 约定：复条目 `(a+ib)/√2`、`a,b∼N(0,1)`（单位方差），小侧 Gram 为 `XXᴴ`（m≤n）或 `XᴴX`（n<m），`φ₁` 最大、`k` 从 1 起算。
- 网络备注：Codex CLI 需走本机代理 `127.0.0.1:7897`（系统代理当前关闭）；调用前设 `HTTPS_PROXY/HTTP_PROXY`，并加 `-c 'service_tier="default"'`（`priority` 不支持 gpt-6-luna）。
- **二进制备注（关键）**：npm 装的 `codex`（0.154.0）调 `gpt-6-luna` 被服务端拒（"not supported when using Codex with a ChatGPT account"）；
  Codex 桌面版自带的 `C:\Users\zxy1117\AppData\Local\OpenAI\Codex\bin\13995fba801849b0\codex.exe`（0.155.0-alpha.16.4）可用，2026-09-28 实测回复 `GPT-6 PING_OK`。
  一律用该路径调用（桌面版更新后哈希目录会变，用 `Get-ChildItem ...\Codex\bin -Recurse -Filter codex.exe` 重新定位）。
- 2026-09-28 Codex 第 1 步进展：`NuttallQBoundary.lean` 现含 `gaussianOddMoment_zero`（`∫₀^∞ r e^{-r²/2}=1`，走 Gamma 积分 p=2,q=1,b=1/2）、
  `gaussianOddMoment_general (N : ℕ)`（无 `0<N` 前提）、`gaussianOddMoment_nuttall`，以及一般整数阶 Bessel 的 `0F1` 展开（`modifiedBesselI_nat_eq_regularizedHG` 等）。单独构建通过。
  **未完成**：`nuttallQ_self_zero`（`Q_{t,t−1}(a,0)=a^{t−1}`）；Codex 三次尝试卡在把复幂指数 `((q:ℝ):ℂ)` 化为自然幂，按执行计划第 7 条撤下未通过代码。
- 2026-09-28 Claude：**G2c 完成** `GramSpectrumTransfer.lean`（已接入 facade，全量构建 3327→ 通过）：
  `charpoly_rowGram_eq_X_pow_mul_charpoly_colGram`（`n≤m` 时 `(AAᴴ).charpoly = X^(m−n)·(AᴴA).charpoly`）、
  `roots_count_eq_of_ne_zero`（非零特征值重数相等）、`count_zero_rowGram_eq_add`、
  `charpoly_paperSmallSideGram_eq_charpoly_colGram`。
  这闭合了 `theory/README.md` 与追踪表 G1 记录的"两种 Gram 非零特征值对应尚未形式化"缺口。
  另把 `finMinEquivLeft/Right`（PaperSmallSideGram）与 `charpoly_submatrix_equiv` 按职责归位为公开引理，消除重复定义。
  (a) 无实质弱化；式 (23) 行列式和=增量概率仍未证（已知缺口）。(b) 缩放 `(a+ib)/√2`、小侧 Gram、`Fin.cast` 次序、`kth` 1-based、φ₁ 最大均一致。
- 2026-09-28 分工协商：Codex 提议 `Theorem3ActualCDF`（带"识别假设"），Claude 否决（联合密度未就绪会把难点塞进假设；T3 常数 1/2 疑点未核实）。
  Codex 接受 **【单列任意 t 统一定理】**，计划：
  1. `NuttallQBoundary.lean`：`Q_{t,t−1}(a,0)=a^{t−1}`；
  2. `SphereAnyDimensionalRadialLaw.lean`：任意 t 球面角积分核（或 Poisson–Gamma 混合路线）；
  3. `NoncentralAnyDimensionalCDF.lean`：一般非中心单列 CDF 化为该核 + 方向不变；
  4. `Theorem1SingleColumnAnyRowsActualCDF.lean`：去 `hden`，候选 = 实际 CDF，并给 Theorem 2 同型结论。
  已派发第 1 步（workspace-write，只写上述新文件，单文件检查）。
