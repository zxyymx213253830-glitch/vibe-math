import JinWishartFormalization.GaussianMatrixBlockLaw
import JinWishartFormalization.GaussianRawCoordinates
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Actual variance-one complex Gaussian column density, every dimension

Codex proof. Transport the existing 2n-real-coordinate Gaussian density through
the already defined real orthonormal column encoding. No new radial integral
or candidate-law assumption. n=0 is allowed.
[需人工审查] Orthonormal/Haar normalization, real vs complex variance convention.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem standardComplexColumnLaw_eq_withDensity (n : ℕ) :
    standardComplexColumnLaw n =
      (volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
        (fun z => ENNReal.ofReal ((Real.pi⁻¹) ^ n * Real.exp (-‖z‖ ^ 2))) := by
  let e := complexColumnCoordinates n
  have hraw := stdGaussian_halfVariance_shift_eq_withDensity n
    (show Fintype.card (Fin n × Fin 2) = 2 * n by simp [Nat.mul_comm])
    (0 : TwoColumnBlock n)
  simp only [add_zero, sub_zero] at hraw
  have hfun : (fun z : EuclideanSpace ℂ (Fin n) => (Real.sqrt 2)⁻¹ • z) ∘ e =
      e ∘ (fun x : TwoColumnBlock n => (Real.sqrt 2)⁻¹ • x) := by
    funext x
    exact (e.map_smul (Real.sqrt 2)⁻¹ x).symm
  unfold standardComplexColumnLaw
  rw [← stdGaussian_map e, Measure.map_map (by fun_prop) e.continuous.measurable,
    hfun, ← Measure.map_map e.continuous.measurable (by fun_prop), hraw]
  have h := map_withDensity_measurePreserving e.toMeasurableEquiv volume volume
    e.measurePreserving
    (fun x : TwoColumnBlock n => ENNReal.ofReal ((Real.pi⁻¹) ^ n * Real.exp (-‖x‖ ^ 2)))
    (by fun_prop)
  refine h.trans ?_
  congr 1
  funext z
  change ENNReal.ofReal ((Real.pi⁻¹) ^ n * Real.exp (-‖e.symm z‖ ^ 2)) = _
  rw [e.symm.norm_map]

end
end JinWishart

#print axioms JinWishart.standardComplexColumnLaw_eq_withDensity
