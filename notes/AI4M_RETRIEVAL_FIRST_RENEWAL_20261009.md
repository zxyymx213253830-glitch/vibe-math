# 董彬指南工具：续开一小时的检索优先记录

用户续开工作窗口：2026-10-09 22:42:03–23:42:03（Asia/Shanghai），即
14:42:03–15:42:03 UTC。此前已提交的 ce08664、eb731cb 不重复计入本窗口。

## 实际调用，而非只列工具名

- LeanSearch：继续用 `verification/leansearch_lookup.ps1`，查询 complex Gaussian
  inner product、characteristic functions、real/complex inner product conversion。
- LeanExplore：按官方 `justincasher/lean-explore` 的 `docs/api-client.md` 与
  `src/lean_explore/api/client.py` 核对公开 GET `/api/v2/search`。
  新增 `verification/leanexplore_lookup.ps1`，支持一条/多条查询、top-k 和 Mathlib
  包筛选。实际调用成功。当前官方说明不需要账号/API key；没有发送任何秘密、
  私有代码或整份仓库。返回源码仅作候选数据，不执行。
- Lean 内核反馈：每个候选核对本地精确类型，再运行局部证明、模块/主构建及公理审计。

LeanExplore 本轮索引源码指向 mathlib 提交
`aae61ae084c21995ee248964a81e3750ad0db2db`；项目锁定
`e18afff334217588afc719a8b707b00d90521064`，Lean v4.35.0-rc2。
不能把线上检索命中视为本项目可直接调用。
官方 API 代码仓库许可证 Apache 2.0；本地脚本是按公开接口写的简短客户端，未复制其实现。
本轮尝试获取服务仓库 main 固定提交时 GitHub API 触发未认证请求限额，
不伪造该版本号，也不为此使用聊天中旧 Token。数学证明仅依赖上述锁定本地 mathlib。

## 候选采用与拒绝

| 候选 | 判定 | 原因 |
|---|---|---|
| `charFun_stdGaussian`、`charFun_map_smul`、`Measure.ext_of_charFun` | 本地采用 | 直接识别复 Gaussian 线性投影的实际推前分布；不重证 Fourier 唯一性 |
| `IsGaussian.charFunDual_eq`、`charFunDual_map` | 保留邻近资产 | 特征函数路线可用，但当前最短证明用有限维 `stdGaussian` 公式 |
| `OrthogonalFamily.independent` | 拒绝作为随机独立定理 | 它是子空间的线性独立性，不是概率随机变量独立性，检索名称不能代替读类型 |
| `Submodule.IsOrtho.starProjection_comp_starProjection` | 确定性投影候选 | 可用于后续残差代数，单独不提供分布/独立性 |
| `real_inner_eq_re_inner` | 需实例核对 | EuclideanSpace 的实际 ℝ 内积实例不与该限制标量实例直接匹配；使用既有极化恒等式比较 |

本地实际复用的概率独立入口仍优先考虑已有检索笔记里的
`HasGaussianLaw.indepFun_of_covariance_inner`，不能重造相同基础定理。

## 额外现成代码的范围核查

读 `openai/math` 固定提交 `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`：
Apache 2.0，Lean v4.34.1；读取 `lean/docs/140.md` 与对应候选源码。

- `lean/OAI/Analysis/TriangularHilbert/GaussianGram.lean` 只给 weighted Gram 的
  缩放/权重正性，不是 Gaussian Gram 密度。拒绝因文件名误用。
- `lean/OAI/Analysis/FreeEntropy/GaussianProjectionMoments.lean` 是投影二阶矩、
  期望/Markov 界，不是本任务所需复条件联合密度。未复制或引入整个项目。

这些是查阅到的特定文件范围结论，不是宣称整个仓库或全球无相关证明。
外部代码未引入就没有“移植验收”可报告。

15:03 UTC 进一步顺官方文档的实际链接读
`lean/ComparatorChallenges/MemoryPrecision.lean`：包含 `AmbientGramStatement`、
`FullRankDensityFormula` 等目标定义，但该文件末尾 `MemoryPrecision.main` 仍用
`sorry`。这是挑战陈述文件，不能当可导入的已完成密度证明；也不能据此断言
仓库里其他证明资产都未完成。未导入或复制任何占位证明。

## 本轮边界

保留原项目版本；reap 需要不同版本兼容和推理服务配置，不通过降级主项目来凑工具使用。
不用大规模训练、付费服务或未经授权上传项目。指南中的工具用于
“精确检索 → 核对类型/版本/许可 → 复用 → 内核验证”，不是自动填补缺失数学。

本地新增引理并不等于全球首创或上游已接收。
测度、复高斯方差及论文模型对应继续 `[需人工审查]`；跨模型家族 P4 尚未完成。

官方来源：[LeanExplore API 文档](https://github.com/justincasher/lean-explore/blob/main/docs/api-client.md)，
[客户端源码](https://github.com/justincasher/lean-explore/blob/main/src/lean_explore/api/client.py)，
[LeanSearch](https://leansearch.net/)。
