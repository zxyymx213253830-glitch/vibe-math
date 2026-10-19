import JinWishartFormalization.GaussianShiftKernelBounds

/-!
# Actual shifted Gaussian measure between two central scalar-covariance laws

Codex. No likelihood-ratio bound at equal variance is claimed.
[需人工审查] Measure order, scale Jacobian and finite-dimensional encoding.
-/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem stdGaussian_smul_eq_density {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : r ≠ 0) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => r • z) =
      volume.withDensity (fun z => ENNReal.ofReal (abs (r^Fintype.card ι)⁻¹)*
        ENNReal.ofReal (euclideanStdGaussianDensity (r⁻¹ • z))) := by
  simpa only [add_zero,sub_zero] using
    stdGaussian_scaled_shift_eq_withDensity r hr (0 : EuclideanSpace ℝ ι)

theorem stdGaussian_shift_measure_lower {ι : Type*} [Fintype ι]
    (y : EuclideanSpace ℝ ι) :
    ENNReal.ofReal (((2 : ℝ)^Fintype.card ι)⁻¹*Real.exp (-‖y‖^2)) •
      (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => (1/2 : ℝ) • z) ≤
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => z+y) := by
  rw [stdGaussian_smul_eq_density (1/2) (by norm_num),stdGaussian_shift_eq_withDensity]
  rw [← withDensity_smul _ (by unfold euclideanStdGaussianDensity; fun_prop)]
  apply withDensity_mono
  apply ae_of_all
  intro z
  have hj : abs (((1/2 : ℝ)^Fintype.card ι)⁻¹) = (2 : ℝ)^Fintype.card ι := by
    simp only [one_div,inv_pow,inv_inv,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2^Fintype.card ι)]
  dsimp only [Pi.smul_apply,smul_eq_mul]
  rw [hj]
  norm_num only [one_div,inv_inv]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  convert (euclideanStdGaussianDensity_shift_bounds z y).1 using 1
  field_simp

theorem stdGaussian_shift_measure_upper {ι : Type*} [Fintype ι]
    (y : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => z+y) ≤
    ENNReal.ofReal ((2 : ℝ)^Fintype.card ι*Real.exp (‖y‖^2)) •
      (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => (2 : ℝ) • z) := by
  rw [stdGaussian_smul_eq_density 2 (by norm_num),stdGaussian_shift_eq_withDensity]
  rw [← withDensity_smul _ (by unfold euclideanStdGaussianDensity; fun_prop)]
  apply withDensity_mono
  apply ae_of_all
  intro z
  dsimp only [Pi.smul_apply,smul_eq_mul]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2^Fintype.card ι)⁻¹)]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  convert (euclideanStdGaussianDensity_shift_bounds z y).2 using 1
  field_simp

end
end JinWishart
#print axioms JinWishart.stdGaussian_smul_eq_density
#print axioms JinWishart.stdGaussian_shift_measure_lower
#print axioms JinWishart.stdGaussian_shift_measure_upper
