# vibe Math

信息论与信息几何研究工作区，围绕两项主要工作组织：可复现的研究工作流，
以及具体命题的形式化验证。

## 工作流

研究流程遵循“先数值、后证明”：先用随机采样寻找反例，再用 `infoq.check`
检查 Shannon 型可证性；LP 未识别的命题继续进入结构化论证。证明路线、实验、
机检脚本和研究台账分别归档，数值证据与证明结论明确区分。

主要内容：

- `infoq/`：信息表达式解析、Shannon 型不等式 LP 判定和数值反例预言机。
- `verification/`：逐步 converse 检查及 LP、数值演示。
- `experiments/`：固定种子的数值实验，并与已知闭式结果对照。
- `notes/`：猜想台账和研究路线记录。
- `AGENTS.md`：供 AI agent 遵循的研究规范与提示词模板。

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

### 每个研究项目怎么跑

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

### 下一步可扩展

- `pip install cvxpy`：凸优化 converse 数值验证（高斯信道、率失真对偶）。
- WSL2 里装 SageMath：信息几何的符号张量计算（α-联络、曲率）。
- Lean 4（elan 安装）：把 1~2 个核心引理形式化进 `theory/`。
- 对接外部工具交叉验证：XITIP（网页版 ITIP）、Aristotle（云端 Lean prover）。

## 具体的形式化验证

当前的 Lean 案例位于 [`theory/jin_wishart_formalization/`](theory/jin_wishart_formalization/)，
以 Jin 等人 2008 年的复 Wishart 矩阵论文为对象，验证其中可与随机矩阵密度公式
分离的确定性论证骨架：Rice 因子的单调性、Gram/Wishart 矩阵半正定性，以及等功率
条件下有序特征模的 SNR 次序。

这是验证 Lean/mathlib 对外围论证覆盖能力的可行性原型，不等同于整篇论文的形式化。
随机矩阵联合密度、特殊函数、行列式 CDF 以及渐近展开相关的测度论细节仍待补齐，
涉及这些部分的证明必须标注 `[需人工审查]`。更多范围说明和构建方法见
[`theory/README.md`](theory/README.md) 与案例目录中的 README。
