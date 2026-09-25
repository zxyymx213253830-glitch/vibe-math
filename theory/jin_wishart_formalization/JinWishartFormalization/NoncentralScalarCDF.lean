import JinWishartFormalization.WishartGamma
import JinWishartFormalization.Theorem1Formula

/-!
# Scalar noncentral bridge for Theorem 1

This module records rigorous scalar reductions toward the noncentral Rice/Nuttall-Q
CDF.  It does not identify the shifted-ball probability with the Nuttall-Q integral;
that analytic angular/radial integral remains a separate theorem.
-/

open Matrix MeasureTheory ProbabilityTheory Set

namespace JinWishart

/-- The real-coordinate representative of a `1 × 1` complex mean has squared
Euclidean length twice the squared modulus of its complex entry.  Thus the
paper's Nuttall-Q noncentrality argument `sqrt (2 * lambda)` is precisely the
length of the real Gaussian translation when `lambda = ‖M₀₀‖²`. -/
theorem complexSampleMean_norm_sq_scalar (M : Matrix (Fin 1) (Fin 1) ℂ) :
    ‖complexSampleMean M‖ ^ 2 = 2 * ‖M 0 0‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [complexSampleMean, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Consequently, the Rice/Nuttall-Q amplitude determined by the scalar
noncentrality `lambda = ‖M₀₀‖²` is exactly the Euclidean length of the shift. -/
theorem complexSampleMean_norm_eq_sqrt_scalarNoncentrality
    (M : Matrix (Fin 1) (Fin 1) ℂ) :
    ‖complexSampleMean M‖ = Real.sqrt (2 * ‖M 0 0‖ ^ 2) := by
  rw [← complexSampleMean_norm_sq_scalar M, Real.sqrt_sq_eq_abs]
  exact (abs_of_nonneg (norm_nonneg (complexSampleMean M))).symm

/-- In the rank-one scalar specialization of Theorem 1, the determinant ratio
reduces exactly to the normalized Nuttall-Q tail.  This is the formula-side
reduction; it does not yet assert that the ratio is the Gaussian Gram CDF. -/
theorem theorem1ScalarNoncentralCandidate_eq_nuttallQ (lambda x : ℝ) :
    theorem1CdfCandidate 1 1 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x =
      1 - ‖nuttallQ 1 0 (Real.sqrt (2 * lambda)) (Real.sqrt (2 * x))‖ /
        ‖nuttallQ 1 0 (Real.sqrt (2 * lambda)) 0‖ := by
  simp [theorem1CdfCandidate, theorem1PsiMatrix, theorem1PsiEntry,
    theorem1QOrder]
  norm_num

/-- In the `1 × 1` rank-one specialization, the formula's Nuttall-Q amplitude
is the length of the actual translated Gaussian center. -/
theorem theorem1ScalarCandidate_uses_shiftNorm
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) :
    theorem1CdfCandidate 1 1 1 (by omega) (by omega)
      (fun _ : Fin 1 => ‖M 0 0‖ ^ 2) x =
      1 - ‖nuttallQ 1 0 ‖complexSampleMean M‖ (Real.sqrt (2 * x))‖ /
        ‖nuttallQ 1 0 ‖complexSampleMean M‖ 0‖ := by
  rw [theorem1ScalarNoncentralCandidate_eq_nuttallQ]
  rw [complexSampleMean_norm_eq_sqrt_scalarNoncentrality]

/-- The scalar noncentral CDF event is the translated planar Gaussian ball.
This packages the existing measure identity next to the scalar formula layer,
so the remaining task is precisely to evaluate this ball mass as the
Nuttall-Q expression above. -/
theorem noncentralScalarCDF_eq_shiftedBall (M : Matrix (Fin 1) (Fin 1) ℂ)
    (x : ℝ) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      (stdGaussian (ComplexSample (m := 1) (n := 1))).real
        (Metric.closedBall (-complexSampleMean M) (Real.sqrt (2 * x))) := by
  rw [cdf_eq_real, measureReal_def]
  rw [noncentralScalarSmallestEigenvalue_sublevelMass_eq_shiftedBall M x hx]
  rfl

end JinWishart
