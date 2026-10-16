# 随机子空间能量律：2026-10-16

用户授权 Codex 与本地 DeepSeek 继续 Lean 研究，背书事宜由用户处理。本批没有启动自动心跳或旧研究循环。

## 已验收范围

`GaussianRandomSubspaceLaw.lean` 的五条声明通过串行 Lean 检查（退出 0），打印公理均为 `propext, Classical.choice, Quot.sound`：

1. 固定正交子空间两侧的半平方范数联合律为 `Gamma(k,1) × Gamma(l,1)`。
2. 半平方范数与环境空间投影／残余表达式相同。
3. 参数化环境投影联合可测，则两侧能量联合可测。
4. 子空间依赖任意参数、两侧实维数几乎处处分别为 `2k,2l` 时，保留整个参数的联合推前律为参数测度与两个 Gamma 测度的乘积。
5. 对实际独立随机变量 `X,Y`，若 `Y` 是标准 Gaussian、子空间仅由 `X` 决定，则上述联合律成立。

`k,l` 都必须严格为正；维数断言允许零测异常。第一、第三条复用现有 Gaussian 独立性及径向 Gamma 资产；第四条调用 mathlib `MeasurePreserving.skew_product`，没有重复证明通用 Fubini。第五条使用显式 `IndepFun X Y P`，不能用于由 `Y` 自身选出的子空间。这是真实 Gaussian 能量律，未把目标密度作为前提。

## 来源与未通过尝试

最终五条证明由 **Codex** 完成。本地 `deepseek-prover-v2:7b` 只收到一个固定的短引理目标及精确资产，最多两次：第一次包含占位证明，解析前拒绝；第二次保留原始证明体检查，`exact?` 未关闭目标，Lean 退出 1 并打印 `sorryAx`。两次请求、完整真实回应、失败原稿及原始检查输出全部保留；没有把其中任何一个算作验收通过的本地成果。Codex 补完同一原目标，没有弱化其假设或结论。本地不承担 P4 审查。

## 控制与复现

`experiments/gaussian_random_subspace_control.py`：seed=20261016，每例 200000 样本，复维数/投影复秩分别为 `(3,1)`、`(5,2)`。投影空间来自独立的前序 Gaussian 列；总能量 Gamma 控制、联合 Gamma CDF、按前序数据的范数与方向分箱的联合 CDF 均通过。故意改成由当前向量自身决定投影时，残余恒零，负面对照通过。数值只是控制，不是证明。

在仓库根目录，用同一资源门串行检查；技术资源门需要一个**新的有效** `state.json`，不得复用已过期的会话：

```powershell
& D:\miniconda3\python.exe tools/deepseek_prover/collaborative_check.py `
  --session NEW_RESOURCE_GATE `
  --source 'D:\vibe math\theory\jin_wishart_formalization\JinWishartFormalization\GaussianRandomSubspaceLaw.lean' `
  --module JinWishartFormalization.GaussianRandomSubspaceLaw `
  --library 'D:\vibe math\.tools\publication-revision-20261016\fresh-project-library' `
  --log 'D:\vibe math\verification\gaussian_random_split_20261016\random-split-1.txt'
& D:\miniconda3\python.exe verification/gaussian_random_split_20261016/audit.py
```

`audit.json` 绑定本模块源码、实际日志、生成的 olean、既有项目依赖闭包、工具链锁定文件及实验源码。检查的是新叶子，**没有重新运行全部构建或更改主入口**。源码 UTF-8；存在一条仅涉及辅助恒等式多余类型类参数的 linter 提示，无内核错误。

## 语义检查与剩余缺口

Codex 自审：半实范数对应复 `CN(0,1)` 能量的尺度约定、`k,l>0`、实维数 `2k,2l`、推前测度上的几乎处处维数、独立新 Gaussian 向量、联合投影可测性均在原声明中明确；参数测度的 `SFinite` 与实际样本源的概率测度假设保留。

**[需人工审查]** 新模块的投影可测性接口、skew-product/Fubini、标准实 Gaussian 到实际复样本的尺度与模型对应。既有 Step 审查不覆盖本模块；本次没有完成新的跨家族 P4 或人工审查。

这尚未给实际前序列空间验证联合可测性、一般满秩与几乎处处维数，也没有得到残余多列完整矩阵律或一般 Cholesky Jacobian。一般实际 Wishart 矩阵密度、G2、原论文一般定理与 T3 常数仍开放。下一张卡应以实际前序列矩阵的 Gram 逆显式投影为对象，验证其与正交投影的相等、联合可测及满秩例外集，再实例化本模块；不能继续只添加假定目标密度的接口。

现有论文、署名、审查快照和投稿 ZIP 均未更改。资源门仅用于串行检查与有限超时，没有额外后台工作承诺；本任务启动的闲置 Ollama 服务已停止，指定模型已卸载，见 `shutdown.json`。
