# P4 独立对抗审查（模型审查，非人工审查）

## 审查范围

仅审查以上四份快照：`GaussianRandomSubspaceLaw.lean`、`GaussianOrthogonalProjectionLaw.lean`、`GaussianOrthogonalSplitLaw.lean`、新增 Gram 投影子模块，以及给出的 `MeasurePreserving.skew_product` mathlib 源码片段。不审查未提供的 Bartlett/QR 实际构造代码、未提供的 Wishart 密度推导代码、前序 Step 审查内容。结论仅基于源码文本推理与所给 Lean 退出码/公理打印，未独立重新编译。

## 问题

未发现阻断性的逻辑错误或可测性/独立性假设被隐藏绕过的具体问题。以下为需标注严重性的观察点：

**[轻微] `stdGaussian_random_split_energy_law` 的 `hdimK`/`hdimC` 为 `∀ᵐ a ∂μ`（几乎处处），但被 `filter_upwards` 合并后直接喂给 `stdGaussian_orthogonal_energy_pair_law`（该引理要求精确等式 `Module.finrank ℝ K = 2*k`）。这一步是正确的（filter_upwards 对 a.e. 性质逐点取值后得到精确等式），没有偷换强度，但读者需注意：零测集上的秩失败不影响结论，这是通过 a.e. 事件的纯粹性保证的，而不是通过某种"近似"论证。**无具体错误**，仅提示该a.e.处理的合法性依赖 `skew_product` 定理本身只要求 fiber 律 a.e. 成立（已在 mathlib 源码中确认：`hg : ∀ᵐ a ∂μa, map (g a) μc = μd`），匹配正确。

**[轻微] 命名误导风险** — `stdGaussian_orthogonal_energy_pair_law` 名称和注释声称是"fixed-fiber"，但在 `stdGaussian_random_split_energy_law` 中被用作该随机子空间每个固定纤维 a 处的律；这是正确用法（随机子空间论证的标准手法：对固定纤维证明，再用 skew-product 粘合），非错误，只是命名在跨文件阅读时容易让人误以为与随机情形无关。

**[信息] Gram 投影子模块中 `totalGramColumnSpaceReal` 在奇异集上退化为 `⊥`（零空间）**——这与注释一致("Use zero on the exceptional singular set")，且 `totalGramColumnSpaceReal_projection` 证明中奇异分支确实验证了 `gramInverseProjector A = 0` 时投影到 `⊥` 也是零映射，逐点匹配正确，没有隐藏不一致。

**[信息] `IndepFun.comp` 用法** — `stdGaussian_orthogonal_energy_pair_law` 中对 `IndepFun` 调用 `.comp` 传入 `φ`、`ψ` 两个几乎处处可测（`fun_prop`生成）的函数，是标准的"函数的函数仍独立"模式，无问题。

## 仍未覆盖的义务（非代码错误，是范围声明）

以下均为文件注释 `[需人工审查]` 中已自陈的缺口，不应被当作本次发现的新问题：

1. **实际 Bartlett/QR 构造中前序列子空间的联合可测性与几乎处处满秩性**未被本次快照证明，仅给出了"若已知联合可测投影+a.e.秩条件，则能推出能量律"的抽象框架。
2. **一般（非对称分块）Jacobian 和一般 Wishart 密度**未被触及，这些文件只处理到"子空间固定或参数化给定、独立高斯向量投影后的 Gamma×Gamma 积律"层面。
3. **复数坐标系与实维度换算的全局一致性**（复 CN(0,1) vs 实高斯半范数惯例）仅在注释层面声明"对应"，未给出复数情形下这组定理的直接复刻版本。
4. **Gram 逆投影子模块与 `GaussianRandomSubspaceLaw` 中 `hproj` 假设的实际拼接**——`measurable_totalGramColumnSpaceReal_projection` 确实提供了形式上匹配的可测性引理，但本次快照中没有看到实际调用处（即把 `K := fun a => totalGramColumnSpaceReal (某前序列矩阵 a)` 代入 `indep_stdGaussian_random_split_energy_law` 的组合证明），因此"供给"关系是潜在可用而非已验证已完成。
5. **a.e.满秩概率的实际计算**（即 Wishart 情形下奇异集测度为零）未被证明，`hdimK`/`hdimC` 仍是外部假设而非从高斯分布性质推出的引理。

## 关于 Lean 编译与公理打印的说明

五个文件公理打印均只含 `propext`、`Classical.choice`、`Quot.sound`，退出码0仅说明这些声明在给定签名下类型检查通过、不依赖额外公理，**不代表**：(i) 签名本身对应真实的 Wishart/Bartlett 应用场景，(ii) 未提供代码中的调用点类型契合，(iii) `sorry` 不存在于本次未展示的其余文件。本次审查未独立重新运行编译器，上述退出码/公理信息为用户提供的既有观察，按要求采信但不作为独立验证证据。
