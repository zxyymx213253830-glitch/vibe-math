# 参考董彬学习指南：实际检索与 T3 证明闭合

依据用户提供的《AI for Mathematics 从入门到前沿的学习指南》（2025-09-28）。
本轮沿用金石 Wishart 论文优先、OFDM 暂缓；旧一小时自动任务保持暂停，不擅自延时。

## 实际采用的工具

使用 [LeanSearch](https://leansearch.net/) 的公开 `/search` 服务，接口模式按
[项目 server.py](https://github.com/frenzymath/LeanSearch/blob/main/server.py) 核对，
只提交公开/通用数学查询，不提交整份仓库或秘密。官网提示其记录查询。
新增 `verification/leansearch_lookup.ps1`，仅打印候选名字/类型/模块，不执行返回证明。
查询有一条和多条两种回归；服务失败时明确报错，不伪造离线答案。

关键查询：

`Sum over all subsets with cardinality one equals sum over singleton subsets`

实际前 3 项：`Finset.subsetSum`、`Finset.powersetCard_one`、`Finset.sum_singleton`。
其中 `powersetCard_one` 在锁定 mathlib 的 `Data/Finset/Powerset.lean` 第 259 行
核实；同时复用 `powersetCard_eq_filter`、`sum_filter` 和 `sum_map`。
线上索引版本没有保证与本项目相同，因此名字检索后必须检查本地源码和编译。

这是新路线：先前三次有限和展开失败后停止的要求仍遵守；本轮不是继续盲试
`simp`，而是用户新指令下用检索到的既有一般定理作结构化改写。

## 已写出的精确定理

`T3CentralNormalizationClosure.lean`：

1. `sum_powerset_card_one`：任意有限集合、任意可交换加法幺半群中，
   对恰好一个元素的子集求和等于对所有单元素子集求和。
2. `theorem3CentralTwoThreeCandidate_eq_mixedRowSum`：已有通用 T3 候选在
   `s=2,t=3,L=0,k=2,x=2` 时确实等于上轮已证的两个显式行列式之和。
3. `theorem3CentralTwoThreeCandidate_gt_one`：此**当前转录候选**的实部严格大于 1。
4. `theorem3CentralTwoThreeCandidate_ne_eventProbability`：它不等于任何概率测度
   下任何事件的概率。检验文件进一步实例化到实际中央复 `3×2` Gaussian 谱事件。

这关闭先前的通用求和 API 缺口，使“两个显式项大于 1”升级到具体转录候选的
严格不可能概率结论。不假设谱密度，不宣称归一化修正后公式已证；
不直接判定正式刊版的定理错误。[需人工审查] 来源版本、`L=0` 边界解释、模型对应。
T3 显示常数和 density-derived 常数仍保留为不同定义。

## 未盲目安装的工具

- [reap 当前 README](https://github.com/frenzymath/reap)：实际核对提交
  `ec5b5ed662c5a045f9407595169170e19329fe6e`；toolchain 为 `v4.28.0-rc1`，
  文档称兼容至 `v4.30.0`，本项目为 `v4.35.0-rc2`。
  还需 policy/value/premise-selection 服务。未改变 lockfile、降级 Lean 或启动付费推理；
  如要采用，应在隔离实验中先核验兼容性和服务配置。
- [LeanExplore](https://www.leanexplore.com/) 可作另一检索候选，本次网页正文无法直接
  抽取，不声称已成功调用；本轮可用 LeanSearch 已实际检索。
- Herald/GAUSS/神经证明器与演化工具不直接提供缺失的谱 Jacobian 定理。
  本轮不因工具名出现在指南里就引入大规模模型训练、账户或新主工程依赖。

## 对核心密度缺口的实际查询

三条自然语言查询分别针对复杂 Gaussian Gram 的 Wishart 密度、Hermitian 谱
Jacobian、酉群 Haar 向球面的推前（每条 top-3）。服务返回 Gram 定义/PSD、
Vandermonde 行列式/谱对角化、一般 Haar 不变性/球面积等邻近资产。
它们不等于所需概率密度或谱换元结论；此次检索未找到直接闭合该桥的结果，
不是宣称全网或所有版本中不存在形式化。

## 验证与后续

原固定种子 T3 数值控制完整重跑退出码 0，200000 个实际中央 `3×2` 样本：
阈值 2 处经验概率 0.827370，归一化积分 0.826263，显示候选 1.652527。
不是信息量线性不等式，infoq Oracle/LP 不适用；数值不是 Lean 证明。
新文件直接编译、目标模块构建退出码 0。
`lake env lean -j1 checks/T3CentralNormalizationClosure.lean` 退出码 0：
通用四行求和回归和实际中央 `3×2` Gaussian 事件不等式均通过。
四个公共 theorem 的公理均仅 `propext / Classical.choice / Quot.sound`。
`lake build JinWishartFormalization --quiet` 主工程构建退出码 0。
`git diff --check` 无空白错误；新 Lean 文件无占位证明或新公理。
检索脚本一条查询及两条查询的实际服务调用均退出码 0，不改变工程依赖。

可重复调用（在仓库根目录）：

```powershell
& '.\verification\leansearch_lookup.ps1' -Queries @(
  'Sum over all subsets with cardinality one equals sum over singleton subsets'
) -TopK 5
```

通用求和引理是既有 mathlib 引理的本地组合，不是全球首创或上游贡献。
核心剩余任务仍是实际 Gaussian 原始样本积分到 Gram/有序谱/角变量的合法测度变换。
独立不同模型家族审查未完成，测度与来源解释继续 [需人工审查]。
