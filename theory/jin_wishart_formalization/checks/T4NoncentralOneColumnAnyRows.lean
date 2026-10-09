import JinWishartFormalization

/-! Regression checks through the main facade, including the zero mean and
the one-row and two-row boundaries. Axiom output is part of the acceptance record. -/

open Filter MeasureTheory ProbabilityTheory Topology

#print axioms JinWishart.euclideanStdGaussianDensity_sub
#print axioms JinWishart.gaussian_shiftedBall_integral_bounds
#print axioms JinWishart.noncentralOneColumnCDF_bounds_by_central
#print axioms JinWishart.noncentralOneColumnSmallestCDF_div_tendsto_factorial
#print axioms JinWishart.noncentralOneColumnSmallestCDF_div_tendsto_frobenius

example (m : ℕ) (hm : 0 < m) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (JinWishart.ComplexSample (m := m) (n := 1))).map
        (JinWishart.complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) x / x ^ m)
      (𝓝[>] 0) (𝓝 ((Nat.factorial m : ℝ)⁻¹)) := by
  simpa using JinWishart.noncentralOneColumnSmallestCDF_div_tendsto_frobenius hm
    (0 : Matrix (Fin m) (Fin 1) ℂ)

example (M : Matrix (Fin 1) (Fin 1) ℂ) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (JinWishart.ComplexSample (m := 1) (n := 1))).map
        (JinWishart.complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x)
      (𝓝[>] 0) (𝓝 (Real.exp (-(‖M 0 0‖ ^ 2)))) := by
  simpa using JinWishart.noncentralOneColumnSmallestCDF_div_tendsto_frobenius
    (by norm_num : 0 < 1) M

example (M : Matrix (Fin 2) (Fin 1) ℂ) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (JinWishart.ComplexSample (m := 2) (n := 1))).map
        (JinWishart.complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x ^ 2)
      (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) * Real.exp (-(∑ i : Fin 2, ‖M i 0‖ ^ 2)))) := by
  simpa using JinWishart.noncentralOneColumnSmallestCDF_div_tendsto_frobenius
    (by norm_num : 0 < 2) M
