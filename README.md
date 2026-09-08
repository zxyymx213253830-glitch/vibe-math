# vibe math — 信息论研究的 AI 机检工作流

这是一个把"AI 提出思路和证明 + 机器负责验收"落到信息论/信息几何领域的
研究工作区。核心是自研的 `infoq` 库（ITIP 数学原理的开源实现，无许可问题），
外加一套给 AI agent 使用的工作规则和提示词模板。

## 环境（已配置好）

- Python: `D:\miniconda3\python.exe`（Miniconda，已加入用户 PATH，永久生效）。
  **新开的终端**里直接敲 `python` 即可；旧终端请用绝对路径。
- 已装: numpy / scipy / sympy。装新包: `python -m pip install 包名`。
- 本仓库不依赖网络即可运行全部演示。

## 30 秒上手

```bat
cd /d "D:\vibe math"

:: 1. LP 判定器: Shannon 型不等式自动证明 (输出人类可读证书)
python verification\demo_shannon_lp.py

:: 2. 数值反例预言机: 找反例 / 检验紧性
python verification\demo_numeric_oracle.py

:: 3. converse 逐步机检: 自动抓出证明里的洞
python verification\demo_converse_check.py

:: 4. Blahut-Arimoto 容量实验模板 (数值 vs 闭式解对照)
python experiments\blahut_arimoto.py
```

## infoq 库速查

### 1) 判定一个信息不等式（相当于本地版 ITIP，带证书）

```python
import infoq

r = infoq.check("I(X;Z) <= I(X;Y)", constraints=["X-Y-Z"])
print(r.status)        # PROVED
for coef, label in r.certificate:   # 人类可读证明证书 (精确有理数)
    print(coef, "x", label)
```

- `PROVED`：命题 = 元素不等式（H(S|T)≥0、I(S;T|U)≥0）的非负组合，
  证书经过精确有理数复核，**这是真正的证明**，可直接抄进论文附录。
- `NOT_IDENTIFIED`：命题不在 Shannon 锥内。**不等于命题为假**
  （Ingleton、Zhang-Yeung 型不等式都在这一类）。此时转向人工/其他工具。
- 约束支持马尔可夫链 `"X-Y-Z"`（自动展开成全部成对条件独立）和
  一般等式 `"I(X;Z|Y) = 0"`。
- 表达式语法：`H(X,Y)`、`H(X|Y,Z)`、`I(X;Y)`、`I(X1,X2;Y|Z)`，
  可线性组合：`2*I(X;Y) - 3/2*H(X,Y,Z) >= 0`。

### 2) 数值反例预言机（动手证明前先跑它）

```python
form = infoq.parse("(H(X,Y,Z)+H(Y)) - (H(X,Y)+H(Y,Z))")  # 要求 >= 0
orc = infoq.Oracle(variables={"X","Y","Z"}, levels=2, seed=7)
out = orc.probe(form, n_samples=200_000)

out["gap"]              # 最小间隙
out["counterexample"]   # True => 找到反例, orc.describe(out["pmf"]) 打印分布
out["tight"]            # True => 不等式紧, 取等分布是证明的极值情形
```

判读纪律：反例 = 构造性否定；紧性 = 证明的路线提示；都不是证明。

### 3) converse 逐步机检

```python
steps = [
    {"claim": "I(X;Z) <= I(X;Z,Y)", "constraints": []},
    {"claim": "I(X;Z,Y) <= I(X;Y)", "constraints": ["X-Y-Z"]},
]
print(infoq.format_report(infoq.check_steps(steps)))
```

任何一步 NOT_IDENTIFIED 即整条 converse 有洞——写论文前先机检一遍，
能挡住绝大多数"看起来显然"的错误步骤。

## 工作流（每个研究项目怎么跑）

```text
猜想 --> infoq 数值扫描 (毙掉假命题)
     --> infoq.check   (PROVED: 拿证书写 LaTeX, 完成)
     --> NOT_IDENTIFIED: 用 AGENTS.md 里的 P1 模板让规划模型分 3 条证明路线
     --> 每条路线一个文件, 机检步骤用 infoq, 人工步骤标 [需人工审查]
     --> P4 对抗审查 (换一个模型家族当审稿人)
     --> LaTeX 进 theory/, 实验进 experiments/, 台账进 notes/
     --> 每个可运行状态 git commit
```

`AGENTS.md` 是给 AI agent 看的操作手册（铁律 + 提示词模板 P1~P5）。
在这个工作区里召唤任何 agent，它都会读到这份手册并遵守同一套纪律。

## 目录约定

| 目录 | 放什么 | 纪律 |
|---|---|---|
| `infoq/` | 核心库 | 改动后必须重跑全部 demo |
| `verification/` | 每个猜想/引理一个机检脚本 | 文件名 = 命题短名 |
| `experiments/` | 数值实验 | 固定种子；必须与闭式解/文献值对照 |
| `theory/` | LaTeX / Lean | 每个定理标注机检状态 |
| `notes/` | 猜想台账、路线分析 | 猜想状态三值: 数值通过 / 已证明 / 已否证 |

## 下一步可扩展

- `pip install cvxpy`：凸优化 converse 数值验证（高斯信道、率失真对偶）。
- WSL2 里装 SageMath：信息几何的符号张量计算（α-联络、曲率）。
- Lean 4（elan 安装）：把 1~2 个核心引理形式化进 `theory/`。
- 对接外部工具交叉验证：XITIP（网页版 ITIP）、Aristotle（云端 Lean prover）。
