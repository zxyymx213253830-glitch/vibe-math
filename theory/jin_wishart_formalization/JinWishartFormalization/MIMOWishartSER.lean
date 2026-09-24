import JinWishartFormalization.WishartProbability
import JinWishartFormalization.GaussianQ

/-!
# Gaussian-Q SER decrement for a noncentral complex Wishart Gram channel

This file connects the scalar layer-cake result to the actual shifted complex
Gaussian sample model.  The resulting formula is an average over the sample
space; identifying it with the paper's closed determinant formulas is still a
separate theorem.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

variable {m n : ℕ}

/-- The least ordered eigenvalue of the noncentral complex Gram channel, as a
random variable on the underlying standard complex Gaussian sample space. -/
noncomputable def noncentralGramLeastEigenvalue
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) :
    ComplexSample (m := m) (n := n) → ℝ :=
  complexNoncentralSampleSmallestEigenvalue M hn

/-- CDF of the SNR-scaled least eigenvalue on the Gaussian sample space. -/
noncomputable def noncentralGramScaledLeastEigenvalueCDF
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) (beta x : ℝ) : ENNReal :=
  statisticCDF (stdGaussian (ComplexSample (m := m) (n := n)))
    (fun z => 2 * beta * noncentralGramLeastEigenvalue M hn z) x

/-- Mean Gaussian-Q decrement for the least eigenmode of a shifted complex
Wishart Gram channel. For nonnegative `beta`, the decrement is the weighted
complement-CDF integral. This theorem uses no density formula for the ordered
eigenvalues and does not yet identify its CDF with Theorem 1's determinant. -/
theorem noncentralGram_meanGaussianQDecrement_eq_cdfComplementIntegral
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∫⁻ z, ENNReal.ofReal
        (gaussianQ 0 - gaussianQ (Real.sqrt
          (2 * beta * noncentralGramLeastEigenvalue M hn z)))
        ∂stdGaussian (ComplexSample (m := m) (n := n)) =
      ∫⁻ t in Ioi 0,
        (1 - noncentralGramScaledLeastEigenvalueCDF M hn beta t) *
          ENNReal.ofReal (gaussianQKernel t) := by
  let f : ComplexSample (m := m) (n := n) → ℝ :=
    fun z => 2 * beta * noncentralGramLeastEigenvalue M hn z
  have hf_meas : Measurable f := by
    dsimp [f, noncentralGramLeastEigenvalue]
    exact measurable_const.mul (measurable_complexNoncentralSampleSmallestEigenvalue M hn)
  have hf_nonneg : 0 ≤ᵐ[stdGaussian (ComplexSample (m := m) (n := n))] f := by
    apply ae_of_all
    intro z
    have hmin : 0 ≤ noncentralGramLeastEigenvalue M hn z := by
      exact complexNoncentralGram_eigenvalues₀_nonneg M z (smallestEigenvalue₀Index hn)
    positivity
  have hmain := meanGaussianQDecrement_eq_cdfComplementIntegral
    (stdGaussian (ComplexSample (m := m) (n := n))) f hf_nonneg hf_meas
  simpa [f, noncentralGramLeastEigenvalue,
    noncentralGramScaledLeastEigenvalueCDF, statisticCDF] using hmain

end JinWishart
