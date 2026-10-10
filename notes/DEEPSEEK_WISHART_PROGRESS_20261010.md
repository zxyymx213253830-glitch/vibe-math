# 本地 DeepSeek 读取进展与实际推进记录

2026-10-10，用户授权调用 Ollama 中专用于 Lean 的本地模型读取当前进展并继续推进。
实际模型名 `deepseek-prover-v2:7b`，本机 Ollama 0.34.1。
没有新建聊天、恢复旧 automation 或启动无限后台循环。

## 交给模型的进展

Codex 阅读了恢复后一小时报告、定理台账、Bartlett 密度预检及实际 Lean 源码，
整理为 `tools/deepseek_prover/wishart_progress_context.md`，通过本地
`http://127.0.0.1:11434/api/generate` 与目标一起发送。
这是明确提供的进展摘要和精确声明，不是声称模型自动读取了整个仓库或全部聊天。
新增 `prove.py --context-file` 支持并保留实际输入，可重复调用。

现状：实际中心 2×2 Gaussian 样本已有独立 Bartlett 坐标律、Gram 推前、
正首能量域的 Jacobian=S 及 Lebesgue 换元。仍缺实际 Bartlett/Gram 密度，
后续联合有序谱密度及论文一般定理亦未完成。

## 本地模型结果：NOT_PROVED

| 任务 | 生成次数 | Lean 拒绝 | 输出含未填目标、提前拒绝 |
|---|---:|---:|---:|
| 完整正支持域图像 | 3 | 2 | 1 |
| 拆分后的行列式恒等式 | 3 | 2 | 1 |
| 提供已验收辅助引理后再次组合 | 3 | 3 | 0 |

共九次生成，**没有任何本地生成证明通过验收**。
失败包括漏用平方根平方引理、错误坐标构造、删掉正残差/正首坐标假设、
不采用已提供引理、留下未填证明和 Lean 语法错误。
工具始终只把证明体放回原始命题，未接受模型擅自改写的陈述。
失败不表示原命题为假，也不能据此估计整个模型的普遍成功率。

三组都使用 8192 上下文、4096 最大生成、temperature=0.6、top_p=0.95，
seed 分别为30、31、32。每次生成后卸载模型，再串行运行 Lean，未升级依赖。
所有实际提示词、模型回答、API 元数据及检查诊断归档在
`tools/deepseek_prover/wishart_research_verification.json`；只省略了 API 的数字 tokenizer 缓存。
原始运行目录仍在 `.tools/prover-runs/wishart-{support,determinant,supported}-20261010/`。

## 实际验收的推进：由 Codex 补充

`JinWishartFormalization/TwoRowGramSupport.lean` 已接入主 facade。
以下四条均由 **Codex 编写**，不归功于本地模型：

1. 正首坐标域的 Gram 图右逆。
2. Gram 四实坐标行列式等于 S×E。
3. 正首坐标且正行列式的逆像残差能量为正。
4. 精确图像等式：

```text
chart '' {p | p0>0 and p3>0}
  = {q | q0>0 and q1^2+q2^2 < q0*q3}.
```

这是下一密度桥所需的确定性定义域衔接。
**没有**证明实际坐标几乎必然落在该域，没有新增概率密度，
没有完成 Gram→谱 Jacobian/角积分或论文一般 Theorem 1–4。

## 验收证据

- `lake build`：退出码0，3363 jobs，主 facade 已编译。
- `checks/TwoRowGramSupport.lean`：退出码0，四条公理审计仅
  `propext`、`Classical.choice`、`Quot.sound`，正/零/负残差三项回归通过。
- 新研究模块无未填证明、新公理或 native_decide。工具目录的
  `*_goal.lean` 是待填输入模板，不能计入已证研究成果。
- 先运行固定seed=202610100155、200000点数值对照：
  逆映射误差4.16e-15，Jacobian det-S误差7.11e-15，
  行列式-S×E误差2.13e-14，有限差分误差2.26e-09；零/负残差边界对照通过。
  对照已知代数恒等式及解析逆映射，数值只是实现控制，不是证明。
  目标为确定性平方根/多项式代数，不是 infoq 可编码的信息量不等式。
- 工具的上下文参数已通过九次实际调用和 Python 语法检查。

[需人工审查] 坐标域与实际 Hermitian 概率模型的对应、边界零质量、
volume 规范及后续测度换元。跨模型家族 P4 测度审查未完成，不称审查通过。
下一步仍是实际 CN(0,1) 密度、乘积密度/坐标重排与边界零质量，
之后才能用既有 Jacobian=S 推得实际 Gram 密度。

未知未跟踪文件保持原状，只提交本次明确文件；未推送远端。
