import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Codex. Seed2026102406: 36 calibrated controls before source.
Nonnegative radial reduction, suitable for Tonelli without integrability assumptions.
[需人工审查] Haar disintegration, removal of the origin and Lebesgue normalization. -/
open MeasureTheory Set Metric
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem lintegral_norm_volume_fin_three (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v : EuclideanSpace ℝ (Fin 3), f ‖v‖) =
      ENNReal.ofReal (4*Real.pi) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^2)*f r := by
  let E := EuclideanSpace ℝ (Fin 3)
  have hs : (volume : Measure E).toSphere univ=ENNReal.ofReal (4*Real.pi) := by
    rw [Measure.toSphere_apply_univ]
    simp only [E,finrank_euclideanSpace, Fintype.card_fin,
      EuclideanSpace.volume_ball_fin_three,ENNReal.ofReal_one,one_pow,one_mul]
    change (3 : ℝ≥0∞)*ENNReal.ofReal (Real.pi*4/3)=_
    rw [show (3 : ℝ≥0∞)=ENNReal.ofReal (3 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    ring
  calc
    _ = ∫⁻ v : ({(0 : E)}ᶜ : Set E), f ‖v.1‖
        ∂((volume : Measure E).comap (Subtype.val : ({(0 : E)}ᶜ : Set E) → E)) := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl (fun v : E => f ‖v‖),
        restrict_compl_singleton]
    _ = ∫⁻ x : sphere (0 : E) 1 × Ioi (0 : ℝ), f x.2 ∂(volume : Measure E).toSphere.prod (Measure.volumeIoiPow 2) := by
      simpa [E] using (volume : Measure E).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
        (Homeomorph.measurableEmbedding _) (f ∘ Subtype.val ∘ Prod.snd)
    _ = (volume : Measure E).toSphere univ *
        ∫⁻ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2 := by
      rw [lintegral_prod _ (by fun_prop)]
      simp [mul_comm]
    _ = _ := by
      rw [hs,Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
      change ENNReal.ofReal (4*Real.pi) *
        (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal ((r : ℝ)^2)*f r
          ∂((volume : Measure ℝ).comap (Subtype.val : Ioi (0 : ℝ) → ℝ)))= _
      rw [lintegral_subtype_comap measurableSet_Ioi (fun r : ℝ => ENNReal.ofReal (r^2)*f r)]

end
end JinWishart
#print axioms JinWishart.lintegral_norm_volume_fin_three
