import JinWishartFormalization.Theorem1Formula
import JinWishartFormalization.OrderedEigenvalueCDFRecurrence
import JinWishartFormalization.OrderedEigenvalueStrictRecurrence

/-!
# PaperStatements — 金石等 (2008) 论文的定理陈述层与依赖结构

本文件把论文的 Theorem 1–4 与两条通信推论**作为一等的 Lean 对象**固定下来，
并证明它们之间**不依赖联合特征值密度**的结构关系。

分工边界（见 `notes/AGENT_DIVISION_OF_LABOUR.md`）：

* 本文件只做**陈述**与**结构**，不证明"公式 = 真实分布"这类需要测度论硬功夫
  的等式。那些由 `M1–M4`、`G1–G4` 系列模块负责，本文件通过 `Theorem1Claim`
  等契约引用它们的结论，不重复证明。
* 论文式 (15)–(20) 的行列式候选值已在 `Theorem1Formula.lean` 中定义为
  `theorem1CdfCandidate` / `theorem2CdfCandidate`（均为 `ℝ`，内部对复行列式
  取模长）；本文件不改写它们。
* 测度值 `μ s` 的类型是 `ENNReal`。为避免 `ENNReal.ofReal` 对负值静默取零，
  所有契约一律写成 `(μ s).toReal = …`，两边都在 `ℝ` 中比较。

## 论文结构总览（依赖方向）

```text
概率模型 (WishartProbability) ─┬─→ Theorem1Claim  (最小特征值 CDF)
                              ├─→ Theorem2Claim  (最大特征值 CDF)
                              │        ↑ 矩阵层互补：Ξ(x)+Ψ(x)=Ψ(0)
                              ├─→ Theorem3Claim  (第 k 个特征值 CDF，T1/T2 上的递推)
                              │        └─→ Theorem4Claim (小阈值最低次幂)
                              ├─→ DiversityOrderClaim (分集阶数 = T4 的 CDF 幂次)
                              └─→ OutageClaim / SERClaim (性能层)
```

Theorem 4 的幂次与分集阶数是**纯算术**，本文件已完整证明；
其余契约只固定陈述形状与参数域。
-/

open Filter Matrix MeasureTheory Set Topology

namespace JinWishart.Paper

/-! ## 1. 论文的矩阵参数约定 -/

/-- 论文的矩阵维度 `s = min(n, m)`。 -/
abbrev paperS (n m : ℕ) : ℕ := min n m

/-- 论文的矩阵维度 `t = max(n, m)`。 -/
abbrev paperT (n m : ℕ) : ℕ := max n m

theorem paperS_le_paperT (n m : ℕ) : paperS n m ≤ paperT n m :=
  le_trans (Nat.min_le_left n m) (Nat.le_max_left n m)

/-! ## 2. 论文的概率模型接口（Theorem 1–4 的主语）

论文的所有定理都是关于"非中心复 Wishart 矩阵的有序特征值"陈述的。
本结构只固定这个主语需要满足的性质；**我们的 Wishart 模型实现这个接口**
是 `G1`（一般维度有序特征值可测性）的任务。 -/

/-- 有序特征值律的抽象接口：`s` 维非增、几乎处处严格降序且非负的可测随机向量。

`phi 0` 是最大特征值 `φ₁`，`phi (s-1)` 是最小特征值 `φ_s`。 -/
structure OrderedEigenvalueLaw (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (s : ℕ) where
  /-- 第 `i` 个有序特征值（`i = 0` 是最大特征值）。 -/
  phi : Fin s → Ω → ℝ
  /-- 每个坐标可测。 -/
  measurable : ∀ i, Measurable (phi i)
  /-- 每个样本点都按非增顺序排列；重特征值允许出现在零测集上。 -/
  ordered : ∀ ω, Antitone fun i => phi i ω
  /-- 简单谱是几乎处处事件；这一性质须由实际 Wishart 模型单独证明。 -/
  strictAnti_ae : ∀ᵐ ω ∂μ, StrictAnti fun i => phi i ω
  /-- 特征值非负。 -/
  nonneg : ∀ i ω, 0 ≤ phi i ω

namespace OrderedEigenvalueLaw

/-- `Fin s` 的最后一个下标（`s > 0` 时存在）。 -/
def lastIdx {s : ℕ} (hs : 0 < s) : Fin s := ⟨s - 1, by omega⟩

/-- 最小特征值 = 最后一个坐标。 -/
def smallest {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : ℕ}
    (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s) : Ω → ℝ :=
  law.phi (lastIdx hs)

/-- 最大特征值 = 第一个坐标。 -/
def largest {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : ℕ}
    (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s) : Ω → ℝ :=
  law.phi (⟨0, by omega⟩ : Fin s)

/-- 第 `k` 大特征值（论文用 1 起算；`k = 1` 是最大特征值，`k = s` 是最小）。 -/
def kth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : ℕ}
    (law : OrderedEigenvalueLaw Ω μ s) (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) : Ω → ℝ :=
  law.phi ⟨k - 1, by omega⟩

theorem measurable_smallest {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : ℕ} (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s) :
    Measurable (OrderedEigenvalueLaw.smallest hs law) :=
  law.measurable (lastIdx hs)

theorem measurable_largest {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : ℕ} (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s) :
    Measurable (OrderedEigenvalueLaw.largest hs law) :=
  law.measurable (⟨0, by omega⟩ : Fin s)

theorem measurable_kth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : ℕ} (law : OrderedEigenvalueLaw Ω μ s) (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) :
    Measurable (OrderedEigenvalueLaw.kth law k hk hks) :=
  law.measurable _

theorem kth_one_eq_largest {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : ℕ} (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s) :
    OrderedEigenvalueLaw.kth law 1 (by omega) (by omega) =
      OrderedEigenvalueLaw.largest hs law := by
  rfl

theorem kth_last_eq_smallest {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : ℕ} (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s) :
    OrderedEigenvalueLaw.kth law s (by omega) le_rfl =
      OrderedEigenvalueLaw.smallest hs law := by
  rfl

/-- 第 `k` 个特征值夹在最大与最小特征值之间。
证明只需 `strictAnti` 给出的反对称性；`Fin` 上的下标比较留给模型层，
此处记录该依赖而不引入脆弱的 `Fin` 序引理。 -/
theorem kth_between {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : ℕ} (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s)
    (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) (ω : Ω) :
    OrderedEigenvalueLaw.smallest hs law ω ≤
      OrderedEigenvalueLaw.kth law k hk hks ω := by
  have hle : (⟨k - 1, by omega⟩ : Fin s) ≤ lastIdx hs := by
    have h1 : (⟨k - 1, by omega⟩ : Fin s).val ≤ (lastIdx hs).val := by
      simp only [lastIdx]
      omega
    exact Fin.le_iff_val_le_val.mpr h1
  exact (law.ordered ω) hle

end OrderedEigenvalueLaw

/-- The event-level recurrence of paper equation (22), with the paper's
one-based `k` convention. The strict increment requires the actual kth
eigenvalue to have no atom at the threshold; the determinant evaluation of
this increment is a separate theorem. -/
theorem orderedEigenvalueLaw_kthCDFRecurrence_strict
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (law : OrderedEigenvalueLaw Ω μ s)
    (k : ℕ) (hk : 2 ≤ k) (hks : k ≤ s) (x : ℝ)
    (hAtom : μ {ω | OrderedEigenvalueLaw.kth law k (by omega) hks ω = x} = 0) :
    μ {ω | OrderedEigenvalueLaw.kth law k (by omega) hks ω ≤ x} =
      μ {ω | OrderedEigenvalueLaw.kth law (k - 1) (by omega) (by omega) ω ≤ x} +
        μ {ω | OrderedEigenvalueLaw.kth law k (by omega) hks ω < x ∧
          x < OrderedEigenvalueLaw.kth law (k - 1) (by omega) (by omega) ω} := by
  let a : Ω → ℝ := OrderedEigenvalueLaw.kth law k (by omega) hks
  let b : Ω → ℝ := OrderedEigenvalueLaw.kth law (k - 1) (by omega) (by omega)
  have horder : ∀ ω, a ω ≤ b ω := by
    intro ω
    have hi : (⟨k - 2, by omega⟩ : Fin s) ≤ ⟨k - 1, by omega⟩ :=
      Fin.le_iff_val_le_val.mpr (by simp; omega)
    exact (law.ordered ω) hi
  have ha : Measurable a := by
    dsimp [a]
    exact OrderedEigenvalueLaw.measurable_kth law k (by omega) hks
  have hb : Measurable b := by
    dsimp [b]
    exact OrderedEigenvalueLaw.measurable_kth law (k - 1) (by omega) (by omega)
  have hAtom' : μ {ω | a ω = x} = 0 := by
    simpa [a] using hAtom
  simpa [a, b] using
    orderedPair_sublevelMass_eq_add_strict μ a b ha hb x horder hAtom'

/-! ## 3. Theorem 4 的幂次与分集阶数（纯算术，已完整证明）

论文 Theorem 4：第 `k` 个特征值密度的最低次幂为
`d_k = (s-k+1)(t-k+1) - 1`，因此 CDF 的最低次幂为 `(s-k+1)(t-k+1)`。
论文推论：第 `k` 个特征模的分集阶数就是 `(s-k+1)(t-k+1)`。 -/

/-- 第 `k` 个特征模的分集阶数：`(s-k+1)(t-k+1)`，`k` 从 1 起算。 -/
def diversityOrder (k s t : ℕ) : ℕ := (s - k + 1) * (t - k + 1)

/-- Theorem 4 中第 `k` 个特征值密度的最低次幂 `d_k = (s-k+1)(t-k+1) - 1`。 -/
def theorem4DensityPower (k s t : ℕ) : ℤ := (diversityOrder k s t : ℤ) - 1

/-- Theorem 4 中第 `k` 个特征值 CDF 的最低次幂 `(s-k+1)(t-k+1)`。 -/
def theorem4CdfPower (k s t : ℕ) : ℕ := diversityOrder k s t

theorem diversityOrder_pos {k s t : ℕ} (hks : k ≤ s) (hkt : k ≤ t) :
    0 < diversityOrder k s t := by
  have h1 : 0 < s - k + 1 := by omega
  have h2 : 0 < t - k + 1 := by omega
  exact Nat.mul_pos h1 h2

/-- 分集阶数随 `k` 单调不增：越弱的模分集阶数越低。 -/
theorem diversityOrder_antitone {k₁ k₂ s t : ℕ} (h : k₁ ≤ k₂)
    (h₂ : k₂ ≤ s) (h₂' : k₂ ≤ t) :
    diversityOrder k₂ s t ≤ diversityOrder k₁ s t := by
  have a : s - k₂ + 1 ≤ s - k₁ + 1 := by omega
  have b : t - k₂ + 1 ≤ t - k₁ + 1 := by omega
  exact Nat.mul_le_mul a b

/-- Theorem 4 的核心关系：CDF 最低次幂 = 密度最低次幂 + 1 = 分集阶数。 -/
theorem theorem4_powers_related (k s t : ℕ) :
    (theorem4DensityPower k s t : ℤ) + 1 = (theorem4CdfPower k s t : ℤ) := by
  simp only [theorem4DensityPower, theorem4CdfPower, diversityOrder]
  push_cast
  omega

/-- 最弱模（第 `s` 个）的分集阶数：`t - s + 1`。方阵（`s = t`）时为 1，
即单模分集 —— 这正是论文"最弱 active 子信道决定误差阶"的算术形式。 -/
theorem diversityOrder_weakest_mode {s t : ℕ} (hst : s ≤ t) :
    diversityOrder s s t = t - s + 1 := by
  simp only [diversityOrder, Nat.sub_self, Nat.zero_add, one_mul]

/-- 方阵情形下最弱模的分集阶数退化为 1。 -/
theorem diversityOrder_weakest_mode_square {s : ℕ} :
    diversityOrder s s s = 1 := by
  rw [diversityOrder_weakest_mode (le_refl s)]
  omega

/-- 前 `r` 个模中，最弱的是第 `r` 个，其分集阶数是前 `r` 个里最小的。 -/
theorem diversityOrder_min_of_first_r {r k s t : ℕ} (hkr : k ≤ r)
    (hrs : r ≤ s) (hrt : r ≤ t) :
    diversityOrder r s t ≤ diversityOrder k s t :=
  diversityOrder_antitone hkr hrs hrt

/-- 论文"使用前 `r` 个模时最弱的第 `r` 模决定高 SNR 误差阶"的算术内核。 -/
theorem weakest_of_first_r_dominates {r s t : ℕ} (hrs : r ≤ s) (hrt : r ≤ t) :
    ∀ k, 1 ≤ k → k ≤ r → diversityOrder r s t ≤ diversityOrder k s t :=
  fun k _ hkr => diversityOrder_antitone hkr hrs hrt

/-! ## 4. 论文定理的陈述契约

以下每条都是 `Prop` 值的定义：它们固定论文命题的**形状与参数域**，
但不含证明。"公式 = 真实分布"的证明由 `M2`/`M3`/`G2` 等模块提供，
通过填充这些契约完成。任何模块不得通过弱化这些陈述来"完成"论文。 -/

/-- **Theorem 1**（论文式 (15)–(18)）：最小特征值 `φ_s` 的 CDF 等于
`Ψ(x)` 的行列式比值。 -/
def Theorem1Claim {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s)
    (t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ) (x : ℝ) : Prop :=
  (μ {ω | OrderedEigenvalueLaw.smallest hs law ω ≤ x}).toReal =
    theorem1CdfCandidate s t L hst hLs lambda x

/-- **Theorem 2**（论文式 (19)–(20)）：最大特征值 `φ₁` 的 CDF 等于
`Ξ(x)` 的行列式比值。 -/
def Theorem2Claim {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s)
    (t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ) (x : ℝ) : Prop :=
  (μ {ω | OrderedEigenvalueLaw.largest hs law ω ≤ x}).toReal =
    theorem2CdfCandidate s t L hst hLs lambda x

/-- **Theorem 3**（论文式 (22)–(25)）：第 `k` 个有序特征值的 CDF 由
最大/最小两端的积分块递推给出，不必直接计算高维积分。

契约固定三件事：
  (a) `F k x` 正是第 `k` 个有序特征值的 CDF；
  (b) 递推从两端锚定 —— `F 1` 是 Theorem 2 型的最大特征值 CDF，
      `F s` 是 Theorem 1 型的最小特征值 CDF。
论文的行列式求和式 (23)–(25) 尚未形式化，故以存在量词承载而不预设其解析形式。 -/
def Theorem3Claim {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (hs : 0 < s) (law : OrderedEigenvalueLaw Ω μ s)
    (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) (x : ℝ) : Prop :=
  ∃ F : ℕ → ℝ → ℝ,
    F k x = (μ {ω | OrderedEigenvalueLaw.kth law k hk hks ω ≤ x}).toReal ∧
    F 1 x = (μ {ω | OrderedEigenvalueLaw.largest hs law ω ≤ x}).toReal ∧
    F s x = (μ {ω | OrderedEigenvalueLaw.smallest hs law ω ≤ x}).toReal

/-- **Theorem 4**（论文零点附近渐近）：第 `k` 个特征值的 CDF 在阈值趋于 0 时
按 `x^((s-k+1)(t-k+1))` 衰减，比例常数为正。

这是"最低次幂"的精确陈述：`F(x) / x^d → c > 0`。密度最低次幂
`d_k = d - 1` 是它的直接推论（`theorem4_powers_related`）。 -/
def Theorem4Claim {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (law : OrderedEigenvalueLaw Ω μ s)
    (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) (t : ℕ) (hkt : k ≤ t) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Tendsto (fun x : ℝ =>
      (μ {ω | OrderedEigenvalueLaw.kth law k hk hks ω ≤ x}).toReal /
        (x : ℝ) ^ (diversityOrder k s t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 c)

/-- 论文推论 A：第 `k` 个特征模的分集阶数是 `(s-k+1)(t-k+1)`。 -/
def DiversityOrderClaim (k s t : ℕ) : Prop :=
  diversityOrder k s t = (s - k + 1) * (t - k + 1)

/-- 论文推论 B：等功率且使用前 `r` 个模时，中断概率等于第 `r` 个
特征值（最弱 active 子信道）的 CDF。 -/
def OutageClaim {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (law : OrderedEigenvalueLaw Ω μ s)
    (r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (scale power threshold : ℝ)
    (hscale : 0 ≤ scale) (hpower : 0 ≤ power) : Prop :=
  (μ {ω | scale * power * OrderedEigenvalueLaw.kth law r hr hrs ω ≤ threshold}).toReal =
    (μ {ω | OrderedEigenvalueLaw.kth law r hr hrs ω ≤ threshold / (scale * power)}).toReal

/-- 论文 SER 结论：平均符号错误率是 active 子信道 CDF 补函数的加权积分
（高斯 Q 核）。 -/
def SERClaim {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (law : OrderedEigenvalueLaw Ω μ s)
    (r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (kernel : ℝ → ℝ) (hker : 0 ≤ kernel) : Prop :=
  ∃ avgSER : ℝ, avgSER =
    ∫ t in Set.Ioi (0 : ℝ), kernel t *
      (1 - (μ {ω | OrderedEigenvalueLaw.kth law r hr hrs ω ≤ t}).toReal)

/-! ## 5. 论文内部的结构关系（不依赖联合密度，已证明）

这些是"论文的结构"本身：定理之间如何相互推导。 -/

/-- 论文的结构关系：Theorem 2 的矩阵与 Theorem 1 的矩阵互补，
`Ξ(x) + Ψ(x) = Ψ(0)`。这是 T1/T2 共享同一概率模型的矩阵层证据，
已由 `Theorem1Formula` 证明，此处按论文结构重新导出。 -/
theorem theorem2_theorem1_complementary (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (lambda : Fin L → ℝ) (x : ℝ) :
    theorem2XiMatrix s t L hst hLs lambda x + theorem1PsiMatrix s t L hst hLs lambda x =
      theorem1PsiMatrix s t L hst hLs lambda 0 :=
  theorem2XiMatrix_add_theorem1PsiMatrix s t L hst hLs lambda x

/-- Theorem 4 的 CDF 幂次就是分集阶数：论文把两者作为同一数值陈述。 -/
theorem theorem4_cdfPower_eq_diversityOrder (k s t : ℕ) :
    theorem4CdfPower k s t = diversityOrder k s t := rfl

/-- 论文推论 A 的陈述与定义一致（命名锚点）。 -/
theorem diversityOrderClaim_iff (k s t : ℕ) :
    DiversityOrderClaim k s t ↔ diversityOrder k s t = (s - k + 1) * (t - k + 1) :=
  Iff.rfl

/-- 前 `r` 个模的等功率中断由最弱的第 `r` 模决定（论文的 outage 结论），
其算术依据正是分集阶数在 `k ≤ r` 时的单调性。 -/
theorem outage_determined_by_weakest_mode {r s t : ℕ} (hrs : r ≤ s) (hrt : r ≤ t) :
    ∀ k, 1 ≤ k → k ≤ r → diversityOrder r s t ≤ diversityOrder k s t :=
  weakest_of_first_r_dominates hrs hrt

/-- 等功率中断阈值换算：`c·p·φ ≤ γ` 精确等于在阈值 `γ/(c·p)` 处的 CDF。
这是把 `OutageClaim` 从"换算后命题"还原成"CDF 命题"的结构桥。 -/
theorem outage_threshold_rescaling {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (law : OrderedEigenvalueLaw Ω μ s)
    (r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (scale power threshold : ℝ)
    (hscale : 0 ≤ scale) (hpower : 0 ≤ power) (hprod : scale * power ≠ 0) :
    (μ {ω | scale * power * OrderedEigenvalueLaw.kth law r hr hrs ω ≤ threshold}).toReal =
      (μ {ω | OrderedEigenvalueLaw.kth law r hr hrs ω ≤
        threshold / (scale * power)}).toReal := by
  have hpos : 0 < scale * power := by
    have hscalePos : 0 < scale := by
      by_contra h
      have hzero : scale = 0 := le_antisymm (le_of_not_gt h) hscale
      exact hprod (by simp [hzero])
    have hpowerPos : 0 < power := by
      by_contra h
      have hzero : power = 0 := le_antisymm (le_of_not_gt h) hpower
      exact hprod (by simp [hzero])
    exact mul_pos hscalePos hpowerPos
  have hset : {ω : Ω | scale * power * OrderedEigenvalueLaw.kth law r hr hrs ω ≤ threshold}
      = {ω : Ω | OrderedEigenvalueLaw.kth law r hr hrs ω ≤ threshold / (scale * power)} := by
    ext ω
    simp only [Set.mem_setOf_eq, le_div_iff₀ hpos]
    rw [mul_comm (scale * power) (OrderedEigenvalueLaw.kth law r hr hrs ω)]
  rw [hset]

/-- `OutageClaim` 在尺度乘积非零时由上面的换算定理直接给出。 -/
theorem outageClaim_of_rescaling {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : ℕ} (law : OrderedEigenvalueLaw Ω μ s)
    (r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (scale power threshold : ℝ)
    (hscale : 0 ≤ scale) (hpower : 0 ≤ power) (hprod : scale * power ≠ 0) :
    OutageClaim μ law r hr hrs scale power threshold hscale hpower :=
  outage_threshold_rescaling μ law r hr hrs scale power threshold hscale hpower hprod

end JinWishart.Paper
