import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.LiminfLimsup

/-! Nonnegative integral divergence from an AE limit of infinite nonnegative mass.
Codex. No monotonicity or false real-Bochner infinity premise.
[需人工审查] Fatou/filter and real-vs-ENNReal interpretation.
-/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem tendsto_integral_atTop_of_ae_limit_lintegral_top {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (F : ℝ → α → ℝ) (g : α → ℝ)
    (hmeas : ∀ r, AEStronglyMeasurable (F r) μ)
    (hint : ∀ᶠ r in atTop, Integrable (F r) μ)
    (hnonneg : ∀ᶠ r in atTop, ∀ᵐ a ∂μ, 0 ≤ F r a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun r => F r a) atTop (𝓝 (g a)))
    (htop : (∫⁻ a, ENNReal.ofReal (g a) ∂μ) = ⊤) :
    Tendsto (fun r => ∫ a, F r a ∂μ) atTop atTop := by
  have hfat := lintegral_liminf_le' (u := (atTop : Filter ℝ))
    (fun r => (hmeas r).aemeasurable.ennreal_ofReal)
  have he : (∫⁻ a, liminf (fun r => ENNReal.ofReal (F r a)) atTop ∂μ) =
      ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hlim] with a ha
    exact (ENNReal.tendsto_ofReal ha).liminf_eq
  rw [he,htop] at hfat
  have ht : Tendsto (fun r => ∫⁻ a, ENNReal.ofReal (F r a) ∂μ) atTop (𝓝 ⊤) :=
    tendsto_of_le_liminf_of_limsup_le hfat le_top
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  apply ht.congr'
  filter_upwards [hint,hnonneg] with r hi hn
  exact (ofReal_integral_eq_lintegral_ofReal hi hn).symm

end
end JinWishart
#print axioms JinWishart.tendsto_integral_atTop_of_ae_limit_lintegral_top
