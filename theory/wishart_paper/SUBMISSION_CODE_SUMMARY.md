# 论文代码提交说明

本说明对应当前主张清单和哈希验收快照，不表示已经投稿或获得独立人工验收。

## 应提交的材料

1. **论文源码**：`main.tex` 是唯一排版入口；现有 `wishart_latex_source.zip` 仅包含它，不包含 Lean 代码。TeX仅放在上传包根目录，代码附属ZIP不再复制TeX。
2. **代码附属文件**：`wishart_formalization_code.zip` 保留原仓库路径、165个 Lean 模块、3份依赖锁/构建配置、119声明的公理审计入口、22项论文主张映射、必要复现工具和两项数值/符号控制。
3. **合并上传包**：`wishart_arxiv_upload.zip` 根目录为 `main.tex`，代码ZIP放在 `anc/` 下。原较大的 `wishart_review_artifact.zip` 是审查交接包，不是默认上传的TeX入口。

这些都是本地材料。署名已按用户指定设为 **ZHOU XINGYUAN**。发布者仍需确认作者认可全文、选择有权授予的许可，并处理尚未关闭的语义审查事项。打包不会自动公开代码。

## 核心代码入口

所有 Lean 模块路径均以 `theory/jin_wishart_formalization/JinWishartFormalization/` 为前缀。

| 对应内容 | 主模块 | 数学强度 |
|---|---|---|
| 实 Gaussian 样本、复编码及 Gram 推前 | `WishartProbability.lean` | 实际模型定义 |
| 随机首列方向与 Bartlett 联合律 | `TwoRowRandomDirectionLaw.lean` | 实际概率律 |
| CN、Bartlett 和 Gram 的密度 | `TwoRowActualDensity.lean`、`TwoRowActualNormalizedDensity.lean` | 中央复2×2的实际密度 |
| 坐标、体积保持和 Jacobian | `TwoRowGramChart.lean`、`TwoRowBartlettCoordinateVolume.lean` | 确定性换元与测度接口 |
| Frobenius 框架规范 | `HermitianCoordinateMetric.lean` | 参考测度乘二、实际密度系数除二 |
| 谱事件、平移锥、最小值 CDF | `TwoRowHermitianThreshold.lean`、`TwoRowSmallestEigenvalueCDF.lean`、`TwoRowMinimumLaw.lean` | 实际最小特征值 Exp(rate=2) |
| 方差缩放 | `TwoRowScaledMinimum.lean` | 振幅a>0、方差a²、率2/a² |
| 原公式中央特例 | `Theorem1CentralTwoRowActualCDF.lean` | 原候选与实际CDF连接；不是一般T1 |
| 非中心单列支撑结果 | `Theorem1TwoRowsActualCDF.lean`、`Theorem1ThreeRowsActualCDF.lean`、`T4NoncentralOneColumnAnyRows.lean` | 明确参数域的实际模型特例/渐近 |
| 对数速率事件 | `TwoRowLogRateOutage.lean` | 单调事件推论；不是总MIMO容量定理 |

不能只提交上述入口。完整证明依赖其余项目模块，包括保持来源标记的本地 DeepSeek `GUIDED_COLLABORATION` 辅助证明体。包内165模块中也有未作为本文已证一般结果的候选/支撑资产；以 `claims.json` 的强度标签为准，不把文件名当成完成一般定理的证据。

## 复现与审查

- Lean 固定为 `leanprover/lean4:v4.35.0-rc2`；mathlib精确版本和传递依赖见 `lake-manifest.json`。不要执行 `lake update` 来改变版本。
- 标准构建入口：在 `theory/jin_wishart_formalization` 中使用相同版本依赖运行 `lake build`。当前报告记录的是全部项目源码的单独串行检查和主入口检查，不冒称已完成整套Lake构建或重建mathlib。
- 实际验收用 `verification/rebuild_wishart_sources.py` 和 `verification/check_publication_axioms.py`；Windows路径适配说明见原 `REPRODUCIBILITY.md`。任何平台适配都应保留工具链版本。
- `experiments/two_row_log_rate_outage.py` 固定seed=20261015、200000个实际Gaussian样本，并检查已知Gamma/Exp控制；`hermitian_coordinate_metric_control.py` 为确定性SymPy检查。依赖为numpy、scipy、sympy。数值结果不是证明。
- `SOURCE_MANIFEST.json` 给出每一份有效载荷的SHA256；打包工具会重开ZIP并逐一验证。代码包不含mathlib缓存、编译产物、模型权重、认证信息、个人应用设置或临时文件。
- 机器验收、模型审查和人工语义审查分别记录。模型真实回应若失败或未覆盖某些证明，不标为通过。

## 尚未完成的范围

一般维度的实际矩阵/联合谱密度G2、原论文一般Theorems 1–4和T3刊版常数解释未完成。Fubini/skew-product、方差/记号及内在Frobenius体积识别仍需独立人工确认。本文已撤下T3归一化诊断，不把已有数值当作刊版勘误。

## 打包后仍由作者决定

署名为ZHOU XINGYUAN，未虚构单位或邮箱；确认论文与代码公开权利和许可；确认是否使用arXiv附属文件或外部固定归档；最终检查arXiv生成的PDF。上述决定不能由电脑用户名、默认软件设置或AI审稿结果代填。
