# 跨模型协作请求：随机列空间投影与下一张满秩卡

用户已授权 Codex 与 Claude Code、Qoder 或 ZCode 合作。当前没有收到有效的外部模型回应。Claude Code 的两次真实只读调用分别在180秒、120秒截止，均无完整回应；没有把它们算作 P4 完成。本文可在你已登录的相应工具中直接打开执行。

请只读证明文件，不修改证明、不运行 Lean 或 Ollama、不升级依赖、不推送、不联系外人。回复可以写入本目录独立的 `EXTERNAL_RESPONSE.md`，保留工具所显示的模型名及实际阅读范围。模型或后端无法确认时明确写未知，不虚构身份。

## 1. 优先完成独立 P4，只报告问题

作者是 Codex，需由不同模型家族独立审查。依次阅读：

- `theory/jin_wishart_formalization/JinWishartFormalization/GaussianRandomSubspaceLaw.lean`
- `theory/jin_wishart_formalization/JinWishartFormalization/GaussianGramProjector.lean`
- `theory/jin_wishart_formalization/JinWishartFormalization/GaussianOrthogonalSplitLaw.lean`
- `theory/jin_wishart_formalization/JinWishartFormalization/GaussianOrthogonalProjectionLaw.lean`
- `verification/gaussian_random_split_20261016/README.md`
- 本目录 `GramProjectorIntegration.lean`，仅是接口组合，不是一般 Wishart 定理。

逐步指出：

1. 是否遗漏联合可测性、SFinite、独立性、实维数、方差约定或 Fubini 假设？
2. 固定正交分裂如何升到由独立前序参数决定的随机分裂？是否错误使用独立性？
3. Gram 逆公式在奇异矩阵处为零；`totalGramColumnSpaceReal` 在该处也取零空间。是否清楚地区分了这与实际奇异列空间的差别？
4. 实/复内积与 Euclidean 坐标转换、满秩处真实实正交投影的相等是否正确？
5. 原目标是否被削弱？注释/README是否声称了尚未证明的满秩概率、维数、一般密度或谱定理？

只报告具体问题并给出声明名及理由，不重写证明。没有发现具体问题也应明确检查范围。Lean 公理清单通过不替代语义审查；模型审查不算人工审查。

## 2. 再做 P1：一般实际 Gaussian 满秩，不写完整证明

下一目标：对 `0 ≤ n ≤ m` 的标准实际中央复 Gaussian `m×n` 前序列矩阵 A，证明 `IsUnit (Aᴴ*A).det` 几乎处处成立，并在其上确认真实列空间的实维数为 `2n`、正交补实维数为 `2(m-n)`。这些概率与维数义务当前仍开放，不能把它们或目标密度作为假设后宣称完成。

比较至少三条不同路线：

1. Gram 行列式作为非零实多项式，利用零集 Lebesgue 零测及实际 Gaussian 对坐标 Lebesgue 的绝对连续性；
2. 逐列独立 Gaussian 与随机前序子空间，利用正余维子空间零测；
3. Gram-Schmidt 或一般 QR/Bartlett 归纳，并精确比较其可测选择开销。

每条列出锁定 mathlib 中实际可找到的精确引理名、最小缺口与循环论证风险。没有核实的名字写 `[待核实]`。不重复既有径向积分、支持代数或2×2实际密度。不要提供以目标密度为前提的替代命题。

## 范围边界

当前成果是一般维数投影接口与真实 Gaussian 能量律，不是一般 Wishart 矩阵/联合谱密度；满秩概率、维数实例、一般 Cholesky Jacobian、G2及原论文一般定理仍开放。测度及论文模型对应继续 `[需人工审查]`。现有论文/发布包与原有 Step 审查快照未更改，新代码不在旧审查范围内。
