import JinWishartFormalization.ScalarGaussianComplexBridge
import JinWishartFormalization.RadialIntegration

/-! Mean-uniform scalar CN1 small-ball bound, a step toward polynomial negative logs.
Codex. No uniform inverse/log-moment conclusion yet.
[需人工审查] Density, disk volume, real-coordinate variance and physical model.
-/
open Matrix MeasureTheory ProbabilityTheory Set
namespace JinWishart
noncomputable section

theorem stdGaussian_complex_closedBall_le_radius_sq_half (μ : ℂ) (R : ℝ) (hR : 0≤R) :
    (stdGaussian ℂ).real (Metric.closedBall μ R) ≤ R^2/2 := by
  let S := Metric.closedBall μ R
  have hi : IntegrableOn (fun z : ℂ => (2*Real.pi)⁻¹*Real.exp (-(‖z‖^2)/2)) S :=
    (show Continuous (fun z : ℂ => (2*Real.pi)⁻¹*Real.exp (-(‖z‖^2)/2)) by fun_prop).continuousOn.integrableOn_compact
      (isCompact_closedBall μ R)
  have hc : IntegrableOn (fun _z : ℂ => (2*Real.pi)⁻¹) S :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall μ R)
  have hV : (volume : Measure ℂ).real S=R^2*Real.pi := by
    simp [S,Measure.real,Complex.volume_closedBall,ENNReal.toReal_ofReal hR]
  rw [stdGaussian_complex_ball_real_eq_densityIntegral]
  calc
    _ ≤ ∫ _z in S, (2*Real.pi)⁻¹ := integral_mono hi hc (fun z => by
      apply mul_le_of_le_one_right (by positivity)
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg ‖z‖])
    _ = _ := by
      rw [setIntegral_const,hV,smul_eq_mul]
      field_simp
      <;> ring

theorem actual_noncentralScalarCDF_le_threshold_uniform_mean
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0≤x) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x ≤ x := by
  rw [noncentralScalarCDF_eq_shiftedBall M x hx]
  rw [measureReal_def,scalarGaussian_shiftedBall_eq_complexBall M]
  change (stdGaussian ℂ).real
    (Metric.closedBall (-((Real.sqrt 2:ℂ)*M 0 0)) (Real.sqrt (2*x)))≤x
  calc
    _ ≤ (Real.sqrt (2*x))^2/2 := stdGaussian_complex_closedBall_le_radius_sq_half _ _ (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sq_sqrt (by positivity)]; ring

end
end JinWishart
#print axioms JinWishart.stdGaussian_complex_closedBall_le_radius_sq_half
#print axioms JinWishart.actual_noncentralScalarCDF_le_threshold_uniform_mean
