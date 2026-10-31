# Wishart 形式化进度评估（2026-10-31）

## 结论

按「金石等 (2008) T1–T4 + 性能公式逐项形式化」这个原始目标，当前约 **50%**（区间 45–55%），处于 **第 3/5 阶段：一般非中心谱桥**。  
按仓库自定的 1118 项验收口径约 **70%**；按 12 页方法论文正文约 **90%**，按可投稿状态约 **65%**。

**分母不同，数字不同。** 本页默认分母是原始论文目标，不是 12 页稿，也不是 binding 数。

## 数据快照（2026-10-31）

- 1118 绑定项（1116 theorem/instance + 2 constructions）
- auditPASS / facade176 exit0
- 216 acceptance records verified
- fullLake / Linux independent kernel: NOT_RUN
- 冻结发表产物: unchanged（12 页稿仍是 2026-10-16 的 305 项快照）
- 最新增量: T3 公式侧（Psi/Xi 行列式和、candidate count、降序参数桥），不是实际联合谱

## 三个分母

| 分母 | 完成度 | 说明 |
|---|---:|---|
| 金石 T1–T4 逐项形式化（原始目标） | ~50% | 本页默认 |
| 仓库自定扩展目标（1118 项验收口径） | ~70% | 扩展结果多，核心 G2/T1-T2/T3 仍 OPEN |
| 12 页方法论文：正文 | ~90% | 中央 2×2 链完整 |
| 12 页方法论文：可投稿 | ~65% | 人审/许可/fresh-source/arXiv 未完成 |

## 50% 的加权口径

| 维度 | 权重 | 当前 | 依据 |
|---|---:|---:|---|
| 陈述/契约 | 15% | 60% | 中央/单列锁定；一般 T1/T2 契约弱，T3 契约不完整 |
| 基础设施 | 25% | 75% | Gaussian/Gram/谱/行列式/特殊函数大量；非中心 G2 的 Jacobian/酉积分缺 |
| 模型→公式 | 25% | 50% | 中央一般已闭合；非中心一般只有迹/Laplace/谱和，不是联合谱 |
| 公式→结论 | 20% | 40% | T3 公式侧强；概率桥 `p=c3ΣdetΘ` 与刊版 `c3` 未闭合；T4 精确常数部分 |
| 独立审查/可复现 | 15% | 15% | 人审未完成；fullLake/Linux kernel NOT_RUN；稿子冻结 |
| **加权** | **100%** | **~50%** | 9 + 18.75 + 12.5 + 8 + 2.25 = 50.5 |

## 为什么 1118 项不等于 50% 以上

- 1118 是绑定项，含大量代数/辅助声明；状态页反复写「非 N 个概率突破」。
- 最近 10 天增量主要在 T3 公式侧，不是实际联合谱。
- 最新条目明确写："Does not establish actual Wishart joint law or displayed journal c3 normalization."
- 路线 review 的下一步是 "a genuine multivariate transform or a concrete matrix-to-spectrum Jacobian"。

## 阶段 3/5

| 阶段 | 内容 | 估计 |
|---|---|---:|
| 1 模型/测度/基础设施 | Gaussian→Gram→谱可测/无原子/行列式/特殊函数 | 85% |
| 2 中央与低维特例 | 中央任意维密度/CDF/PDF、单列、2×2、T4 单列 | 90% |
| 3 一般非中心 G2 + T1/T2/T3 概率桥 | 联合谱密度、Jacobian、酉积分、T3 概率桥 | 40% |
| 4 性能公式 + 论文整合 | 一般 SER/outage、T1–T4 全映射、稿子回灌 | 25% |
| 5 独立审查/全量构建/发布 | 人审、fullLake、Linux kernel、arXiv | 10% |

当前在 stage 3 的公式侧：candidate 代数已深，actual → candidate 的联合谱桥未接上。

## 终局 gate（按「全文收口」）

| Gate | 状态 |
|---|---|
| A 实际非中心联合谱 G2 / matrix-to-spectrum Jacobian | 未过 |
| B 一般 T1/T2 candidate = actual CDF | 未过 |
| C T3 概率桥 `p=c3ΣdetΘ` + 刊版 `c3` 裁决 | 未过 |
| D 一般 T4 精确常数 + 一般 SER/outage | 部分 |
| E fullLake + Linux kernel + 人审 + 稿子回灌 + release | 未过 |

**0/5 完全通过**；但每个 gate 的前置资产已建很多。这就是「50% 资产、0 个终局 gate」。

## 最影响百分比的 3 件事

1. 实际非中心联合谱 / matrix-to-spectrum Jacobian。过了它，T1/T2/T3 一起动。
2. T3 刊版 `c3` 归一化裁决。源文献问题，不是 Lean 问题；决定 T3 概率桥能不能合法写。
3. 人审 + fullLake + Linux kernel + 稿子回灌。决定「可投稿」，目前 0% 量级；不会因为再多 500 个 binding 自动完成。

## 口径提醒

- 形式化百分比不是线性的：最后 20%（G2 + 人审）可能和前面 80% 一样久。
- 不要用 1118 除论文定理数；binding 数不是定理覆盖数。
- 本页是进度评估，不是完成声明；所有 `[需人工审查]` 边界不变。

## 证据

- [WISHART_STATUS.md](WISHART_STATUS.md)
- [JIN_WISHART_THEOREM_TRACKER.md](JIN_WISHART_THEOREM_TRACKER.md)
- [THEOREM_COVERAGE_AUDIT.md](THEOREM_COVERAGE_AUDIT.md)
- [WISHART_ACTUAL_JOINT_LAW_ROUTE_REVIEW_20261031.md](WISHART_ACTUAL_JOINT_LAW_ROUTE_REVIEW_20261031.md)
- [WISHART_LIBRARY_CONTRIBUTION_MAP.md](WISHART_LIBRARY_CONTRIBUTION_MAP.md)
- [main.tex](../theory/wishart_paper/main.tex)
