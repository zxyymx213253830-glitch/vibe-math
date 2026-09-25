import JinWishartFormalization.WishartProbability
import JinWishartFormalization.GaussianRadialCDF

open MeasureTheory ProbabilityTheory

namespace JinWishart

private theorem partialGamma_nat_eq_realLower (m : ℕ) (hm : 0 < m) (x : ℝ) :
    Complex.partialGamma (m : ℂ) x =
      ((∫ u in (0 : ℝ)..x, u ^ (m - 1) * Real.exp (-u) : ℝ) : ℂ) := by
  rw [Complex.partialGamma]
  have hexp : (m : ℂ) - 1 = ((m - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hm]
    norm_num
  have hfun : (fun u : ℝ ↦ (-u).exp * (u : ℂ) ^ ((m : ℂ) - 1)) =
      (fun u : ℝ ↦ ((u ^ (m - 1) * Real.exp (-u) : ℝ) : ℂ)) := by
    funext u
    rw [hexp, Complex.cpow_natCast]
    push_cast
    ring
  rw [hfun, intervalIntegral.integral_ofReal]

private theorem upperGammaNatFinite_eq_real (k : ℕ) (x : ℝ) :
    upperGammaNatFinite k x =
      ((Nat.factorial k : ℝ) * Real.exp (-x) *
        ∑ j ∈ Finset.range (k + 1), x ^ j / (Nat.factorial j : ℝ) : ℝ) := by
  simp [upperGammaNatFinite, Complex.ofReal_exp, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_sum]

private theorem upperGammaNatFinite_norm_eq (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖upperGammaNatFinite k x‖ =
      (Nat.factorial k : ℝ) * Real.exp (-x) *
        ∑ j ∈ Finset.range (k + 1), x ^ j / (Nat.factorial j : ℝ) := by
  rw [upperGammaNatFinite_eq_real]
  apply Complex.norm_of_nonneg
  have hsum : 0 ≤ ∑ j ∈ Finset.range (k + 1),
      x ^ j / (Nat.factorial j : ℝ) := by
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)
  positivity

/-- The integer-shape Gamma CDF is the normalized finite complement used by
the central scalar specialization of Theorem 1. -/
theorem cdf_gammaMeasure_nat_eq_finiteComplement (m : ℕ) (hm : 0 < m)
    (x : ℝ) (hx : 0 ≤ x) :
    cdf (gammaMeasure (m : ℝ) 1) x =
      1 - ‖upperGammaNatFinite (m - 1) x‖ / (Nat.factorial (m - 1) : ℝ) := by
  rw [cdf_gammaMeasure_nat_eq_lowerGamma m hm x hx,
    upperGammaNatFinite_norm_eq (m - 1) x hx]
  have hcomp := upperGammaNat_add_partialGamma (m - 1) x
  have hshape : ((m - 1 + 1 : ℕ) : ℂ) = (m : ℂ) := by
    congr 1
    omega
  have hGamma : Complex.GammaIntegral (m : ℂ) =
      (Nat.factorial (m - 1) : ℂ) := by
    rw [← hshape, ← upperGammaNat_zero_eq_GammaIntegral (m - 1),
      upperGammaNat_at_zero_eq_factorial]
  rw [hshape, hGamma, upperGammaNat_eq_finite (m - 1) hx,
    upperGammaNatFinite_eq_real, partialGamma_nat_eq_realLower m hm x] at hcomp
  have hreal :
      (Nat.factorial (m - 1) : ℝ) * Real.exp (-x) *
          ∑ j ∈ Finset.range (m - 1 + 1), x ^ j / (Nat.factorial j : ℝ) +
        ∫ u in (0 : ℝ)..x, u ^ (m - 1) * Real.exp (-u) =
        (Nat.factorial (m - 1) : ℝ) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_add]
    exact hcomp
  have hrange : m - 1 + 1 = m := by omega
  rw [hrange] at hreal ⊢
  have hfact : (Nat.factorial (m - 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m - 1)
  field_simp [hfact]
  nlinarith [hreal]

/-- The energy in an `m × 1` central complex Gaussian sample is Gamma with
shape `m` and unit rate. This is the scalar Gram/Wishart law before passing
through the smallest-eigenvalue map. -/
theorem centralColumnSampleEnergy_map_eq_gammaMeasure {m : ℕ} (hm : 0 < m) :
    (stdGaussian (ComplexSample (m := m) (n := 1))).map
      centralColumnSampleEnergy = gammaMeasure (m : ℝ) 1 := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  letI : Nontrivial (EuclideanSpace ℝ ((Fin m × Fin 1) × Fin 2)) := inferInstance
  have henergy : centralColumnSampleEnergy =
      euclideanGaussianEnergy (ι := ((Fin m × Fin 1) × Fin 2)) := by
    funext x
    exact centralColumnSampleEnergy_eq_euclideanEnergy x
  rw [henergy]
  apply stdGaussian_euclideanEnergy_map_eq_gammaMeasure m ?_ hm
  simp
  omega

/-- The smallest eigenvalue of the central one-column Wishart sample has the
same integer-shape Gamma law. -/
theorem centralColumnSmallestEigenvalue_map_eq_gammaMeasure {m : ℕ} (hm : 0 < m) :
    (stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin m) (Fin 1) ℂ)
        (by norm_num)) = gammaMeasure (m : ℝ) 1 := by
  have hfun : complexNoncentralSampleSmallestEigenvalue
      (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num) = centralColumnSampleEnergy := by
    funext x
    exact centralColumnSampleSmallestEigenvalue_eq_energy hm x
  rw [hfun, centralColumnSampleEnergy_map_eq_gammaMeasure hm]

/-- For every positive number of rows, the central one-column Wishart
smallest-eigenvalue CDF agrees with the `s=1, L=0` specialization of
Theorem 1. -/
theorem theorem1CentralOneColumn_eq_sampleSmallestEigenvalueCDF
    (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 ≤ x) :
    theorem1CdfCandidate 1 m 0 (by omega) (by omega)
        (fun j : Fin 0 ↦ Fin.elim0 j) x =
      cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) x := by
  rw [centralColumnSmallestEigenvalue_map_eq_gammaMeasure hm]
  rw [theorem1CentralScalarCdfCandidate_eq_finite m (by omega) x hx,
    cdf_gammaMeasure_nat_eq_finiteComplement m hm x hx]

/-- In the same central one-column setting, Theorem 2's lower-incomplete-Gamma
formula is the Gamma CDF. In a one-column model the largest and smallest
eigenvalues are the same scalar. -/
theorem theorem2CentralOneColumn_eq_gammaCDF
    (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 ≤ x) :
    theorem2CdfCandidate 1 m 0 (by omega) (by omega)
        (fun j : Fin 0 ↦ Fin.elim0 j) x = cdf (gammaMeasure (m : ℝ) 1) x := by
  have hdetx :
      (theorem2XiMatrix 1 m 0 (by omega) (by omega)
        (fun j : Fin 0 ↦ Fin.elim0 j) x).det = Complex.partialGamma (m : ℂ) x := by
    rw [Matrix.det_fin_one]
    simp [theorem2XiMatrix, theorem2XiEntry, theorem1GammaIndex]
    congr 1
    exact_mod_cast (show m - 1 + 1 = m by omega)
  rw [theorem2CdfCandidate, hdetx,
    theorem1CentralScalarPsiDet m (by omega)]
  rw [partialGamma_nat_eq_realLower m hm x]
  have hnonneg :
      0 ≤ ∫ u in (0 : ℝ)..x, u ^ (m - 1) * Real.exp (-u) := by
    apply intervalIntegral.integral_nonneg hx
    intro u hu
    exact mul_nonneg (pow_nonneg hu.1 _) (Real.exp_nonneg _)
  rw [Complex.norm_of_nonneg hnonneg,
    cdf_gammaMeasure_nat_eq_lowerGamma m hm x hx]
  norm_cast
  ring

/-- Theorem 2's central one-column candidate is the CDF of the actual
smallest-eigenvalue random variable (equivalently, the unique/largest
eigenvalue) for every positive integer row count. -/
theorem theorem2CentralOneColumn_eq_sampleSmallestEigenvalueCDF
    (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 ≤ x) :
    theorem2CdfCandidate 1 m 0 (by omega) (by omega)
        (fun j : Fin 0 ↦ Fin.elim0 j) x =
      cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) x := by
  rw [centralColumnSmallestEigenvalue_map_eq_gammaMeasure hm]
  exact theorem2CentralOneColumn_eq_gammaCDF m hm x hx

end JinWishart
