# AGENTS.md — AI agent 在本仓库工作的操作手册

本仓库是一个面向**信息论 / 信息几何研究**的机检工作流。任何 AI agent（ZCode、
Claude Code、Codex 等）进入本仓库工作时，必须遵守本手册。

## 环境事实

- Python 解释器: `D:\miniconda3\python.exe`（Miniconda，已装入用户 PATH；
  旧开着的终端可能没有新 PATH，一律用绝对路径调用最稳）。
- 已装依赖: numpy, scipy, sympy。cvxpy 未装，需要凸优化实验时先
  `D:\miniconda3\python.exe -m pip install cvxpy`。
- SageMath 在 Windows 不可用；如需 SageManifolds/编码理论库，用 WSL2。
- 本仓库 Python 代码一律 UTF-8；终端输出避免生僻 Unicode 符号。

## 仓库结构

```text
infoq/            核心库
  expr.py         信息表达式解析: I(X;Y|Z) 等价
  shannon_lp.py   Shannon 型不等式 LP 判定器 (Yeung 元素不等式, 输出精确证书)
  numeric.py      数值反例预言机 (随机采样 + Nelder-Mead 精修)
  converse.py     converse 证明逐步机检
verification/     机检脚本 (每个猜想/引理一个文件)
experiments/      数值实验 (固定种子, 必须与已知闭式解/文献值对照)
theory/           LaTeX 或 Lean 形式化
notes/            研究笔记 (猜想台账、路线分析)
```

## 铁律（按优先级排序）

1. **先数值后证明**。拿到任何猜想，第一件事是用 `infoq.numeric.Oracle` 扫反例，
   LP 可判的用 `infoq.shannon_lp.check`。数值不通过的猜想不进入人工证明阶段。
2. **ITIP/LP 语义必须准确**：
   - `PROVED` = 该不等式是元素不等式的非负组合（证书已用精确有理数复核），
     这是**无条件的证明**（在所给约束下）。
   - `NOT_IDENTIFIED` ≠ 命题为假。它只说明命题不在 Shannon 锥内
     （如 Ingleton、Zhang-Yeung 型），需要更深的论证。绝不可向用户陈述
     "LP 失败所以命题错误"。
3. **数值证据不是证明**。紧而不等（gap≈0）的假命题数值上发现不了，
   向用户汇报时必须区分"反例"（构造性的）、"紧性提示"（启发式）、"证明"（LP 证书或人工）。
4. **测度论细节是 agent 的弱项**。可测性、Fubini、极限交换、正则性假设，
   agent 写的这类步骤必须显式标注 `[需人工审查]`，不得伪装成已完成。
5. **实验必须可复现**：固定随机种子；每个实验与某个已知闭式解/文献值对照；
   对照失败 = 实验实现有 bug（参考 experiments/blahut_arimoto.py 的格式）。
6. **引用纪律**：给用户的文献引用，不确定存在的一律标 `[待核实]`。
7. **每次"可运行状态"提交一次 git**（演示通过、实验完成、文档更新）。

## 标准研究循环

```text
猜想 --> 1. infoq.numeric.Oracle 反例扫描 (不过关: 毙掉或修正)
     --> 2. infoq.shannon_lp.check (PROVED: 完成, 拿证书写 LaTeX)
     --> 3. NOT_IDENTIFIED: 判断是"非Shannon型"(转向结构化论证)
            还是"漏了约束/变量"(回到 1)
     --> 4. 分路线证明 (见提示词模板 P1), 每条路线独立文件
     --> 5. 对抗审查 (见 P4), 输出 [需人工审查] 清单
     --> 6. LaTeX 入 theory/, 实验入 experiments/, 台账更新入 notes/
```

## 常用 API 速查

```python
import sys; sys.path.insert(0, r"D:\vibe math")   # 从任意位置导入 infoq
import infoq

# LP 判定 (Shannon 型可证性), 支持马尔可夫链约束
r = infoq.check("I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])
r.status        # "PROVED" / "NOT_IDENTIFIED"
r.certificate   # [(Fraction, 元素不等式标签), ...] 人类可读证明证书

# 数值反例扫描
form = infoq.parse("(H(X,Y,Z)+H(Y)) - (H(X,Y)+H(Y,Z))")   # 线性形式 >= 0
orc = infoq.Oracle(variables={"X","Y","Z"}, levels=2, seed=7)
out = orc.probe(form, n_samples=200_000)
out["gap"], out["counterexample"], out["tight"], orc.describe(out["pmf"])

# converse 逐步机检
steps = [{"claim": "I(X;Z) <= I(X;Z,Y)", "constraints": []}, ...]
report = infoq.format_report(infoq.check_steps(steps))
```

## 提示词模板（与其他模型协作时使用）

### P1 路线分化（给规划模型）

```text
你是一位信息论专家。研究背景：[一段，说明信道模型和已有结果]。
待证命题：[精确陈述，含全部假设]。
请完成，不要写完整证明：
1. 列出命题依赖的所有隐含假设（可测性、有限性、正则性、马尔可夫关系）。
2. 给出 3 条本质不同的证明路线（例如：凸对偶/LP、方法类型/组合、信息几何/投影），
   每条写出：核心引理清单、文献中最接近的已知结果、最可能的失败模式。
3. 为每条路线的每个关键步骤标注机检类型：
   [infoq-LP 可判 / 凸优化数值可验 / SymPy-Sage 符号可验 / 只能人工审查]。
4. 指出哪条路线的核心引理最少、哪条最容易被机器部分验证。
```

### P2 数值预言机（给执行 agent；在本仓库直接执行）

```text
为以下猜想构造 infoq 数值预言机脚本并运行：
猜想：[...]（写成 A >= B 的信息不等式，或含约束）
要求：levels 覆盖 2 和 3；n_samples >= 200000；报告最小间隙、紧性、反例分布。
```

### P3 ITIP 翻译（给执行 agent；在本仓库直接执行）

```text
把以下信息论不等式翻译成 infoq.check 的调用并运行：
[文字/公式陈述，包括所有马尔可夫条件]。
步骤：先用一句话复述你理解的变量依赖关系，等确认后再写代码。
若结果为 NOT_IDENTIFIED，讨论该不等式是否可能属于非 Shannon 型，
并检查 Zhang-Yeung 不等式族。
```

### P4 对抗审查（必须用与写证明不同的模型家族）

```text
你是苛刻的审稿人。以下证明中，逐步标注：
(a) 用了哪些未声明的假设（可测性、Fubini、极限交换、凸性、维度）；
(b) 哪些"显然成立"的步骤实际需要引理支撑；
(c) 陈述与证明是否自洽——证明的强度是否弱于或偏离了陈述。
只报告问题，不要重写证明。
[证明全文]
```

### P5 文献定位（带防幻觉机制）

```text
以下是我想证明的命题及其路线：[...]。
请列出与每个关键步骤对应的已知经典结果（定理名 + 作者 + 年份），
标注哪些可直接引用、哪些需要重新证明。
只引用你确定存在的文献；任何不确定的条目必须标注 [待核实]，
不允许为凑完整性而猜测出处。
```
