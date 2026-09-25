import JinWishartFormalization.ScalarNoncentralCDFRice
import JinWishartFormalization.ScalarNoncentralTheorem1

/-!
# Theorem 2 in the one-dimensional noncentral case

The paper's Theorem 2 is formula (19)--(20), with `Ξ(x)` built from lower
Nuttall-Q differences and lower incomplete gamma entries. The repository
already defines this determinant-ratio candidate as `theorem2CdfCandidate`;
this file verifies its noncentral `s=t=L=1` specialization and connects that
formula, conditionally, to the completed Rice radial CDF bridge. The analytic
normalization and improper-integrability assumptions remain explicit.
-/

open Matrix MeasureTheory ProbabilityTheory

namespace JinWishart

/-- Nuttall-Q difference appearing in equation (20) for the `1×1`, rank-one
noncentral case. Here the paper's indices are `p=1`, `q=0`. -/
noncomputable def theorem2ScalarNuttallIncrement (lambda x : ℝ) : ℂ :=
  nuttallQ 1 0 (Real.sqrt (2 * lambda)) 0 -
    nuttallQ 1 0 (Real.sqrt (2 * lambda)) (Real.sqrt (2 * x))

/-- Exact scalar reduction of the Theorem 2 maximum-eigenvalue determinant
ratio. In dimension `1×1`, the sole eigenvalue is both largest and smallest;
formula (20) reduces to a single Nuttall-Q difference over the Theorem 1
normalizer. -/
theorem theorem2ScalarNoncentralCandidate_eq_NuttallIncrementRatio
    (lambda x : ℝ) :
    theorem2CdfCandidate 1 1 1 (by omega) (by omega)
      (fun _ : Fin 1 => lambda) x =
      ‖theorem2ScalarNuttallIncrement lambda x‖ /
        ‖nuttallQ 1 0 (Real.sqrt (2 * lambda)) 0‖ := by
  simp [theorem2CdfCandidate, theorem2XiMatrix, theorem2XiEntry,
    theorem1PsiMatrix, theorem1PsiEntry, theorem1QOrder,
    theorem2ScalarNuttallIncrement] <;> norm_num

/-- The `1×1` noncentral Theorem 2 candidate agrees with the actual Gaussian
Gram CDF, conditional on total Rice-tail normalization and integrability.
These are analytic facts, not consequences of the determinant algebra. -/
theorem theorem2ScalarCandidate_eq_noncentralCDF_of_Q_normalized
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x)
    (hint : IntegrableOn (nuttallQIntegrand 1 0 ‖complexSampleMean M‖) (Set.Ioi 0))
    (hQ : nuttallQ 1 0 ‖complexSampleMean M‖ 0 = 1) :
    theorem2CdfCandidate 1 1 1 (by omega) (by omega)
      (fun _ : Fin 1 => ‖M 0 0‖ ^ 2) x =
      cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x := by
  have hQ' :
      nuttallQ 1 0 (Real.sqrt (2 * ‖M 0 0‖ ^ 2)) 0 = 1 := by
    simpa [complexSampleMean_norm_eq_sqrt_scalarNoncentrality] using hQ
  rw [theorem2ScalarNoncentralCandidate_eq_NuttallIncrementRatio,
    theorem2ScalarNuttallIncrement, hQ', norm_one, div_one]
  rw [← complexSampleMean_norm_eq_sqrt_scalarNoncentrality M]
  rw [← hQ]
  rw [← noncentralScalarCDF_eq_nuttallQ_difference M x hx hint]
  simp [Complex.norm_real, ProbabilityTheory.cdf_nonneg]

/-- Unconditional `1×1` noncentral Theorem 2 formula: because the sole Gram
eigenvalue is both the largest and smallest eigenvalue, the normalized Rice
tail mass and integrability results close the scalar probability identity. -/
theorem theorem2ScalarCandidate_eq_noncentralCDF
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x) :
    theorem2CdfCandidate 1 1 1 (by omega) (by omega)
      (fun _ : Fin 1 => ‖M 0 0‖ ^ 2) x =
      cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x := by
  exact theorem2ScalarCandidate_eq_noncentralCDF_of_Q_normalized M x hx
    (nuttallQ_10_integrand_integrableOn_Ioi _ (norm_nonneg _))
    (nuttallQ_10_zero_eq_one _ (norm_nonneg _))

end JinWishart
