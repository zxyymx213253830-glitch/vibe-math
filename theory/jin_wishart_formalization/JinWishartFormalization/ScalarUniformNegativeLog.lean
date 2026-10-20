import JinWishartFormalization.ProbabilityNegativeLogBounds
import JinWishartFormalization.ScalarUniformSmallBall

/-! Actual scalar CN1 negative-log moment, uniformly in the deterministic mean.
Codex. [需人工审查] Model variance, probability pushforward and logarithmic expectation.
-/
open Matrix MeasureTheory ProbabilityTheory Set
namespace JinWishart
noncomputable section

theorem actual_noncentralScalar_negativeLog_uniform_mean
    (M : Matrix (Fin 1) (Fin 1) ℂ) :
    Integrable (fun z : ComplexSample (m := 1) (n := 1) =>
      max 0 (-Real.log (complexNoncentralSampleSmallestEigenvalue M (by norm_num) z)))
      (stdGaussian _) ∧
    (∫ z : ComplexSample (m := 1) (n := 1),
      max 0 (-Real.log (complexNoncentralSampleSmallestEigenvalue M (by norm_num) z))
      ∂(stdGaussian _)) ≤ 1 := by
  apply negativeLog_integrable_integral_le_of_smallball (stdGaussian _)
    (complexNoncentralSampleSmallestEigenvalue M (by norm_num))
    (measurable_complexNoncentralSampleSmallestEigenvalue M (by norm_num))
    1 (by norm_num)
  intro x hx
  have h := actual_noncentralScalarCDF_le_threshold_uniform_mean M x hx.le
  rw [cdf_eq_real, measureReal_def, Measure.map_apply
    (measurable_complexNoncentralSampleSmallestEigenvalue M (by norm_num)) measurableSet_Iic] at h
  have hpre : (complexNoncentralSampleSmallestEigenvalue M (by norm_num) ⁻¹' Iic x) =
      {z | complexNoncentralSampleSmallestEigenvalue M (by norm_num) z ≤ x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
  rw [hpre] at h
  simpa [measureReal_def] using h

end
end JinWishart
#print axioms JinWishart.actual_noncentralScalar_negativeLog_uniform_mean
