# DeepSeek-Prover-V2-7B 本地使用

本机通过已有的 Ollama 运行 DeepSeek-Prover-V2-7B 的 **Unsloth Q4_K_M GGUF 量化版**。
这是指定模型的第三方格式转换和量化，不是 DeepSeek 官方 BF16 权重直接运行。
量化权重 4,223,362,304 字节，保存在 `D:\OllamaModels`，不放入 Git。

2026-10-10 安装验收：权重 SHA-256 一致；31/31 层加载到 RTX 5070 Ti Laptop；
8K 上下文下观察到约 7.65 GiB 显存占用。模型生成的算术示例通过 Lean 检查，
公理依赖只有 `propext`、`Classical.choice`、`Quot.sound`。Lean 拒绝了对 `0 = 1` 的错误证明。
详细记录见 `verification.json`，模型原样生成并验收的代码见 `verified_example.lean`。
这只是安装测试，不能代表研究级证明成功率。

## 打开模型

双击本目录的 `Start-Prover.cmd`，或者在 PowerShell 输入：

```powershell
& 'D:\Ollama\ollama.exe' run deepseek-prover-v2:7b
```

优先提供明确的 Lean 4 命题、可用定义和相关引理；这个模型主要用于证明补全。
可以直接粘贴如下请求：

````text
Complete the following Lean 4 code. Keep the statement unchanged.
Give a brief proof plan and then the complete code. Do not use sorry or new axioms.

```lean4
theorem demo (n : Nat) : n + 0 = n := by
  sorry
```
````

退出聊天：输入 `/bye`。停止并释放模型显存：

```powershell
& 'D:\Ollama\ollama.exe' stop deepseek-prover-v2:7b
```

## 自动生成并交给 Lean 检查

双击 `Run-Example.cmd`，或在 PowerShell 执行：

```powershell
& 'D:\miniconda3\python.exe' 'D:\vibe math\tools\deepseek_prover\prove.py'
```

默认读取 `example.lean`，最多尝试两次；第一次失败后，将实际 Lean 错误发给模型修复。
已有示例使用模型官方说明里的算术题：120% 的 30 减去 130% 的 20，绝对值为 10。
已知参考证明是 `norm_num`。这是安装演示，不能用于推断研究命题上的成功率。

验证复用本仓库已安装的 Lean 4.35.0-rc2 和 mathlib 编译缓存，不升级项目、不改研究文件。
输出保存在 `D:\vibe math\.tools\prover-runs\时间戳\`，包含原始命题、提示词、模型输出、候选证明和检查日志。
本机内存为 16GB，自动流程会在生成完成后卸载模型，再启动 Lean 检查；示例只导入需要的 mathlib 模块。
检查还关闭隐式参数自动创建，避免拼错名称被意外当作新参数。

- `LEAN_CHECK_PASSED`：保留了输入定理陈述的候选证明通过 Lean；仍需确认输入陈述符合数学意图。
- `NOT_PROVED`：有限次尝试没有得到通过检查的证明，不能理解为命题为假。
- 模型回答“证明完成”本身不是验证结果。
- 黄色的多余战术警告与证明错误不同；本次示例有多余战术警告，但检查成功。

## 证明自己的引理

新建 UTF-8 的 `my_goal.lean`，例如：

```lean
theorem my_goal (a b : Nat) : a + b = b + a := by
  sorry
```

执行：

```powershell
& 'D:\miniconda3\python.exe' 'D:\vibe math\tools\deepseek_prover\prove.py' 'D:\你的目录\my_goal.lean' --attempts 3
```

这个小工具支持一个顶层、具名 theorem，以及文件末尾唯一的一行 `sorry`。
简单自然数引理可以不导入 mathlib；需要其他数学对象时，显式导入对应模块。
它只提取模型提供的证明体，再放回原命题；不会用模型重新写出的命题替换目标。
它拒绝残留 sorry/admit、新公理、截断输出，并打印定理的公理依赖。
当前仅覆盖简单单文件引理；复杂命名空间、多处待证目标或论文级依赖，需要先分解。

若需要其他已配置且已编译的 mathlib 项目：

```powershell
& 'D:\miniconda3\python.exe' 'D:\vibe math\tools\deepseek_prover\prove.py' 'D:\你的目录\my_goal.lean' --project 'D:\你的 Lean 项目'
```

对应 Lean 工具链仍需安装在本仓库的 `.tools\elan` 下。

## 结合当前研究进展

`--context-file` 可把 UTF-8 进展摘要、已证结果和精确可用引理随目标交给模型；
工具会保存实际提供的上下文和每轮提示词。模型仍不自动访问仓库或执行工具，
研究调度和 Lean 验收由外部代理完成。8K 上下文下应提供精简摘要，长进展须拆卡。

本次 Wishart 交接使用 `wishart_progress_context.md`，先尝试完整正支持域图像，
遇到错误后拆成行列式恒等式。可复现拆分任务：

```powershell
& 'D:\miniconda3\python.exe' 'D:\vibe math\tools\deepseek_prover\prove.py' `
  'D:\vibe math\tools\deepseek_prover\wishart_gram_determinant_goal.lean' `
  --context-file 'D:\vibe math\tools\deepseek_prover\wishart_progress_context.md' --attempts 3
```

这些 `*_goal.lean` 是带唯一待填目标的模型输入模板，不是已验收研究模块。
失败回答也保留，不能用模型的文字“Complete Proof”代替 Lean 检查。

2026-10-10 本次研究交接的九次本地生成均未通过验收；最终支持域引理由
Codex 补充并通过主构建、公理和边界检查，不能算作本地模型独立成果。
完整记录：`notes/DEEPSEEK_WISHART_PROGRESS_20261010.md`；原始尝试归档：
`wishart_research_verification.json`。安装示例的成功不代表本次研究任务成功。

## 参数与 API

本地模型名：`deepseek-prover-v2:7b`。
默认上下文 8192 token、最大生成 4096 token、temperature 0.6、top_p 0.95、seed 30。
自动尝试的 seed 从 30 开始递增；温度、版本、驱动可能影响可复现性。
长定理建议先拆成引理，暂不增加并行数量。

本地服务地址：`http://127.0.0.1:11434`。
可以给其他代理调用 `/api/generate`，指定上述模型名。
该模型没有自动工具执行能力；读取文件、运行 Lean、修复循环由 `prove.py` 或外部代理负责。

若 Ollama 未启动，先打开 Ollama 或 `Start-Prover.cmd`。
若 Lean 提示缺少编译库，先在相应项目准备 mathlib 缓存；本工具不会自动更新依赖。
若检查超过 120 秒，优先缩小导入和引理规模；全量 `import Mathlib` 在内存紧张时可能很慢。
量化可能降低证明能力；未通过时可以换 seed、拆引理或交给更强模型。

## 来源与安装记录

- 原始模型：https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-7B
- 量化模型：https://huggingface.co/unsloth/DeepSeek-Prover-V2-7B-GGUF
- Ollama 与 Hugging Face：https://huggingface.co/docs/hub/en/ollama
- 固定下载版本、大小和 SHA-256：见 `installation.json`。

重新注册本地别名（基础模型已下载时）：

```powershell
& 'D:\Ollama\ollama.exe' create deepseek-prover-v2:7b -f 'D:\vibe math\tools\deepseek_prover\Modelfile'
```
