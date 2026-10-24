import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Codex. Seed2026102409 finite-atomic/negative controls before source.
Ordered-half identity allows atoms because the kernel vanishes on the diagonal.
[需人工审查] Nonnegative product integration and symmetry normalization. -/
open MeasureTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem lintegral_symmetric_ordered_half (μ : Measure ℝ) [SFinite μ]
    (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H)
    (hsym : ∀ x y, H (x,y)=H (y,x)) (hdiag : ∀ x, H (x,x)=0) :
    (∫⁻ z in {z : ℝ × ℝ | z.2<z.1}, H z ∂μ.prod μ) =
      (1/2 : ℝ≥0∞) * ∫⁻ z, H z ∂μ.prod μ := by
  let O : Set (ℝ × ℝ) := {z | z.2<z.1}
  let G := O.indicator H
  have hO : MeasurableSet O := measurableSet_lt measurable_snd measurable_fst
  have hG : Measurable G := hH.indicator hO
  have hp : ∀ z : ℝ × ℝ,H z=G z+G z.swap := by
    rintro ⟨x,y⟩
    by_cases hyx : y<x
    · have hxy : ¬x<y := not_lt.mpr hyx.le
      simp [G,O,hyx,hxy]
    · by_cases hxy : x<y
      · simpa [G,O,hyx,hxy] using hsym x y
      · have he : x=y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
        subst y
        simp [G,O,hdiag]
  have hswap : MeasurePreserving Prod.swap (μ.prod μ) (μ.prod μ) := Measure.measurePreserving_swap
  have hfull : (∫⁻ z,H z ∂μ.prod μ)=(∫⁻ z,G z ∂μ.prod μ)+(∫⁻ z,G z ∂μ.prod μ) := by
    calc
      _ = ∫⁻ z,G z+G z.swap ∂μ.prod μ := lintegral_congr hp
      _ = (∫⁻ z,G z ∂μ.prod μ)+(∫⁻ z,G z.swap ∂μ.prod μ) := lintegral_add_left hG _
      _ = _ := by rw [hswap.lintegral_comp hG]
  rw [← lintegral_indicator hO]
  change (∫⁻ z,G z ∂μ.prod μ)=(1/2 : ℝ≥0∞)*∫⁻ z,H z ∂μ.prod μ
  rw [hfull,← two_mul,← mul_assoc]
  rw [one_div,ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞)≠0)
    (by norm_num : (2 : ℝ≥0∞)≠∞),one_mul]

end
end JinWishart
#print axioms JinWishart.lintegral_symmetric_ordered_half
