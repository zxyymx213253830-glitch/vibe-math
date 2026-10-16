# arXiv 投稿审查报告：Wishart 形式化论文

- 日期：2026-10-16
- 审查对象：`theory/wishart_paper/main.tex`（md5 `a92a833c…`，与 `tmp/pdfs/arxiv-source-check/main.tex` 一致），编译产物 `output/pdf/main.pdf`（12 页，编译于 12:04，无警告）
- 审查人：WorkBuddy（独立于论文证明实现与初稿写作链条之外的复核）
- 审查方式：全部主要定理独立重推；论文内可验证事实声明逐一对照仓库工件；编译日志与 12 页渲染逐页目检；引用独立网络核实；既有 `SELF_REVIEW_20261016.md` / `SUBMISSION_READINESS.md` / `BIBLIOGRAPHY_AUDIT.md` 交叉比对

---

## 总结论

**数学内容没有发现问题。** 主要定理链（Bartlett 律 → Gram 密度 → λ_min ~ Exp(2) → 尺度/中断率）我全部独立重推一遍，公式、归一化常数、Jacobian、证明逻辑均正确；论文中所有可在仓库工件中核对的事实声明（工具链版本、mathlib 修订、AI 工作流计数、数值控制指标、模块数）全部吻合；12 条文献引用属实（其中 Gouëzel、Degenne 两条做了独立网络核实）；编译零警告，12 页渲染干净，源码纯 ASCII、无占位符残留。

**能否投稿取决于三项既有阻塞项**（空署名、无公开可访问工件、未完成独立语义审查）——这三项在既有自审中已记录，本次审查确认仍然开放，它们是真正的拦路项，不是排版问题。

本次审查新发现 5 个应当处理的问题，全部不涉及数学正确性，其中最值得动手的是正文里残留的 `\review` 宏（渲染出来是加粗的 "Human semantic review required."， arXiv 读者会看成没写完的草稿标记）。

---

## 1. 数学内容独立复核

复核方法：不读 Lean 证明，直接用纸笔独立推导每个公式，再与论文陈述对照。

| # | 论文陈述 | 独立复核 | 结论 |
|---|---|---|---|
| 1 | Bartlett 律：Law(S,Z,E)=Gamma(2,1)⊗CN(0,1)⊗Exp(1)，密度 (1) | S=‖h₁‖² 为两个 Exp(1) 之和 → Gamma(2,1) ✓；Z~CN(0,1) 密度 π⁻¹e^(-‖z‖²) ✓；残差能量 E~Exp(1) ✓；三者相乘即论文的 s/π·e^(-(s+a²+b²+e)) ✓ | 正确 |
| 2 | 换元 T(s,a,b,e)=(s,√s·a,√s·b,a²+b²+e)，Jacobian=s | 导数矩阵下三角，对角元 1,√s,√s,1 → det=s ✓；图像正是 D={(u,b,c,v): b²+c²<uv} ✓ | 正确 |
| 3 | Gram 密度 f_W=π⁻¹e^(-(u+v))1_D，积分为 1 | 直接计算 ∫_D e^(-(u+v)) du db dc dv = ∫∫ e^(-(u+v))·πuv du dv = π·1·1 = π，故归一化系数确为 π⁻¹ ✓ | 正确 |
| 4 | λ_min(H*H) ~ Exp(2)，即 P(λ_min>x)=e^(-2x) | 由 (3)+谱阈值判据：∫_{W≻xI} π⁻¹e^(-tr W)dW，平移 W=V+xI 得 e^(-2x)·∫_{V≻0} π⁻¹e^(-tr V)dV = e^(-2x)·1 ✓ | 正确 |
| 5 | Jin 候选 det Ψ(x)=e^(-2x)，det Ψ(0)=1 | det[e^(-x)((x²+2x+2, x+1),(x+1,1))] = e^(-2x)(x²+2x+2-(x+1)²) = e^(-2x) ✓；x=0 时为 1 ✓ | 正确 |
| 6 | 一般系数 K_{s,t}=(π^{s(s-1)/2}∏(t-j)!)⁻¹ | 抽验三例：s=1 → 1/Γ(t)，与标量情形 Gamma(t,1) 吻合 ✓；s=t=2 → π⁻¹，与 (3) 吻合 ✓；s=2,t=3 → 1/(2π)，与 Γ₂(3)=2π 的 Wishart 密度惯例吻合 ✓ | 正确 |
| 7 | 递推 K_{s,t}=K_{s-1,t-1}/(π^{s-1}(t-1)!) | 代数展开一致 ✓ | 正确 |
| 8 | 正交分裂：dim K=2k 时 ‖P_K G‖²/2 ~ Gamma(k,1) | χ²_{2k}/2 即 Gamma(k, rate=1) ✓ | 正确 |
| 9 | 非中心单列渐近 F_M(x)/x^m → e^(-‖M‖²_F}/m! | 实编码后为 R^{2m} 中半径 √(2x) 的球：体积 π^m(2x)^m/m! × 中心密度 (2π)^{-m}e^(-‖M‖²} = x^m/m!·e^(-‖M‖²} ✓；论文的 Cauchy–Schwarz 夹逼方向正确 ✓ | 正确 |
| 10 | 中断率 P{C_min≤R}=1-exp(-2(e^R-1)/(ρa²))，R<0 为 0 | λ~Exp(2/a²)，P(λ≤(e^R-1)/ρ) 直接代入 ✓；C_min≥0 故 R<0 概率为 0 ✓ | 正确 |
| 11 | Frobenius 体积关系：dvol_F = 2^{s(s-1)/2} × 坐标测度 | 每个非对角复方向贡献 Frobenius 长度 √2，二维块体积因子 2；s=2 时 ds_F²=du²+dv²+2db²+2dc² → √det(diag(1,2,2,1))=2 ✓ | 正确 |

**结论：未发现数学错误。** 主链没有"以目标密度为前提"的循环（论文 §2.2 的"三层分离"纪律在正文中确实被执行），方差约定（单位复方差）全文一致，严格/弱谱事件的处理（补集论证）正确。

注意边界：以上是纸面复核，不等于对 165 个 Lean 模块证明体的认证；内核通过 + 我的公式复核双重通过，但"形式对象 ↔ 概率模型解释"的对应仍依赖人工语义审查（论文自己也这么定位）。

---

## 2. 事实声明与工件核对

| 论文声明 | 核对来源 | 结果 |
|---|---|---|
| Lean 工具链 v4.35.0-rc2 | `theory/jin_wishart_formalization/lean-toolchain` = `leanprover/lean4:v4.35.0-rc2` | ✓ |
| mathlib 修订 e18afff334217588afc719a8b707b00d90521064 | 同目录 `lake-manifest.json` 含该哈希 | ✓ |
| 一轮会话 38 次生成 = 2 通过 + 29 Lean 拒绝 + 7 输出拒绝；另 2 次手动调用失败不计入；5 次 P4 审查请求全部无有效产出 | `notes/DEEPSEEK_CODEX_ROUND3_SUMMARY_20261011.md` 原文逐字一致 | ✓ |
| 数值控制：seed 20261015、200000 样本、KS≈0.00238/0.00124、特征值公式最大偏差 <5e-15、15 组参数组合 | `verification/WISHART_LOG_RATE_OUTAGE.json`：seed=20261015、samples=200000、trace KS=0.0023761…、minimum KS=0.0012408…、max error=4.885e-15、rows=15 | ✓（0.00238↔0.002376，0.00124↔0.001241） |
| 164/165 模块、1446.21 秒无复用检查 | `notes/WISHART_STATUS.md` 2026-10-16 条目一致 | ✓ |
| 论文自包含：无外部图片、无自定义类、无本地 \input | 源码全文扫描确认 | ✓ |
| 附录所列 claims.json / REPRODUCIBILITY.md / SUBMISSION_READINESS.md 随稿 | `theory/wishart_paper/` 下三文件均在 | ✓ |

---

## 3. 文献引用核实

12 条全部属实。既有 `BIBLIOGRAPHY_AUDIT.md` 已逐条记录核实来源；我对其中最不易确认的两条做了独立网络核实：

- **Gouëzel, arXiv:2207.12742**： Sébastien Gouëzel, *A formalization of the change of variables formula for integrals in mathlib*, cs.LO, 2022-07-26 ✓（另注：该文正式发表于 CICM 2022 LNCS, DOI 10.1007/978-3-031-16681-5_1，可作备选引用）
- **Degenne, arXiv:2510.04070**： Rémy Degenne, *Markov kernels in Mathlib's probability library*, v1 2025-10-05 / v2 2026-04-23 ✓（论文写 "2025; version 2, 2026" 准确）

其余（Jin 期刊版/preprint、Bartlett、Goodman、Edelman×2、Avigad、Affeldt、mathlib、Tse、arXiv 政策页）与审计记录一致，未发现错配。论文对"不做首次性声明"的纪律执行得很好（§1.1 明确写出检索的局限性）。

---

## 4. 编译与排版

- `main.log` 709 行，**零 warning**：无 overfull/underfull、无 undefined reference、无 multiply-defined
- 12 页全部重新渲染目检：标题页、定理证明环境、两个表格、矩阵公式、参考文献均正常；无溢出、无乱码、无残留模板数据
- 源码纯 ASCII（变音符号用 `\"e` 等 TeX 转义），arXiv TeX Live 编译兼容性最佳
- 无 TODO/FIXME 占位符（grep 命中的 "placeholders" 是 §6.1 论述审计方法的正文，非残留）
- 所用宏包全部为标准 TeX Live 包（amsmat/amsthm/booktabs/microtype/hyperref/xurl 等）

---

## 5. 新发现问题（按严重程度）

### 5.1 【中】正文残留 `\review` 宏——最值得动手的一处

源码定义了 `\newcommand{\review}{…\textbf{Human semantic review required.}\ }`，并在两处调用：

- §2.2 末尾："**Human semantic review required.** The Gaussian encoding, the Hermitian coordinate measure, and the identification with the communication model require independent scrutiny."
- §3 末尾（Prop 3.2 之后）："**Human semantic review required.** Product-measure transport, complex-to-real volume normalization, the orientation of the Gram coordinates, and the inverse Jacobian are retained as explicit items in the independent review packet."

问题：(a) 渲染效果是加粗的编辑批注插在定理证明之间，arXiv 读者和 moderation 会理解为未完成的草稿标记；(b) 内容与 §6.4 "Independent review boundary" 完全重复。

建议：删掉宏定义和两处调用，把这两组条目合并进 §6.4，改成一个编号的 "open review items" 列表（保留诚实披露，去掉草稿感）。如果作者坚持保留原位提示，至少把措辞从 "Human semantic review required" 改为 "Open review item (see §6.4):"，去掉命令式的批注腔。

### 5.2 【中】PDF 元数据全空

当前 `title/author/subject/keywords` 均为空串。建议在 hypersetup 中补 `pdftitle`、`pdfauthor`（署名确定后）、`pdfsubject`、`pdfkeywords`。arXiv 会读取 PDF 元数据，空标题影响索引和引用提取。

### 5.3 【低】`\date{Working manuscript, 16 October 2026}`

arXiv 提交页会显示这个日期串。"Working manuscript" + 硬编码日期对正式投稿不太合适。建议要么 `\date{}`（不显示日期），要么用实际提交日期。与此相关：摘要和附录自称 "working manuscript" 是可以的（arXiv 本就是预印本），但请有意识地决定，而不是留在默认状态。

### 5.4 【低】§6.2 KS 统计量的指代不明

原文："The corresponding Kolmogorov–Smirnov statistics are approximately 0.00238 and 0.00124"——"corresponding" 没有绑定哪个数对应哪个检验。按 JSON：迹-Gamma(4,1) 检验是 0.002376，最小值-Exp(2) 检验是 0.001241。建议写明 "the trace check gives 0.00238 and the minimum check 0.00124"。

### 5.5 【低】无 AMS 学科分类与关键词

非必需，但利于发现性。建议补 62H10（Wishart 分布）、60B20（随机矩阵）、68V20（形式化方法）之类；关键词如 complex Wishart, smallest eigenvalue, Lean, formalization, Bartlett decomposition。

### 5.6 【提示，非错误】摘要密度

摘要把数学主链 + AI 工作流统计（38 次生成、2 次通过、5 次审查失败）压进约 200 词。数学贡献被工作流数字稀释。工作流透明度是本文特色，但可考虑把计数细节留给 §6.3，摘要只留一句 "we document the AI-assisted workflow and its limits"。这是定位选择，不是错误。

---

## 6. 既有阻塞项确认（未变，仍是真拦路项）

与 `SELF_REVIEW_20261016.md` / `SUBMISSION_READINESS.md` 记录一致，本次确认全部仍然开放：

1. **作者栏 `\author{}` 为空**——arXiv 必须有署名人类作者；附录自己也写明"投稿前必须补齐"。
2. **无公开可访问的不可变工件**——形式化主张依赖源码，本地 ZIP 不构成读者可验证的证据；需公开仓库/归档 URL，或把 Lean 源码与证据打包为 arXiv 附属文件（ancillary files）。源码许可也待人类作者决定。
3. **独立语义审查未完成**——此前一次真实 Claude P4 调用因 API 402 失败，本地 deepseek 的反馈已归档且不算数。§6.4 对此的披露本身是诚实的，但只要它挂着，论文就处于"工作稿"状态。

这三项都不是排版能解决的；其中第 3 项其实可以借本次审查部分推进——我做的是公式级与事实级复核（见 §1–3），但明确**不能替代** AGENTS.md 定义的跨家族 P4 与人工对"形式对象↔概率模型"对应的审查。

---

## 7. 投稿前检查单（合并既有清单与本次发现）

| 优先级 | 事项 | 状态 |
|---|---|---|
| 阻塞 | 作者姓名/单位/邮箱，所有作者确认稿件并担责 | 待用户 |
| 阻塞 | 公开工件（仓库/归档 URL 或 arXiv 附属文件）+ 源码许可 | 待用户 |
| 阻塞 | 独立 P4 / 人工语义审查（方差、skew-product、换元、谱事件、记号对应） | 未完成 |
| 中 | 删除 `\review` 宏及两处调用，合并进 §6.4 开放条目列表 | 本次发现，可直接改 |
| 中 | 补 hypersetup PDF 元数据（pdftitle/pdfauthor/pdfsubject/pdfkeywords） | 本次发现 |
| 低 | `\date{}` 或定稿日期；决定 "working manuscript" 措辞去留 | 本次发现 |
| 低 | §6.2 KS 两个数明确指代 | 本次发现 |
| 低 | 补 AMS 分类/关键词 | 本次发现 |
| 低 | 摘要工作流计数是否保留（定位选择） | 本次发现 |
| 操作 | arXiv 分类建议 cs.LO（主）/ math.PR / eess.SP；endorsement 按需 | 待提交人 |

---

## 附：审查边界声明

- 本报告是公式级、工件级、排版级复核，不是对 165 个 Lean 模块全部证明体的人工认证。
- 数值证据不是证明；本报告引用的数值指标仅用于核对论文陈述与工件的一致性。
- 引用核实基于 arXiv/出版商公开页面（2026-10-16 访问）。
- 按仓库铁律：未发现需要标注 [待核实] 的引用；未发现数学反例。
