# theory/ — 证明与形式化

每个研究项目在这里建一个子目录，包含：

- `main.tex` — 论文/证明稿。每个定理旁标注机检状态：
  `[infoq: PROVED 证书号]` / `[数值紧性提示]` / `[需人工审查]`。
- （可选）`lean/` — Lean 4 形式化工程。

## LaTeX 里引用 infoq 证书的格式

```latex
\begin{proof}
每一行都可由元素不等式的非负组合验证；完整机检证书见
verification/<脚本名>.py 的输出（证书已经精确有理数复核）：
目标不等式 $= \sum_i \alpha_i e_i$，$\alpha_i \ge 0$。
\end{proof}
```
