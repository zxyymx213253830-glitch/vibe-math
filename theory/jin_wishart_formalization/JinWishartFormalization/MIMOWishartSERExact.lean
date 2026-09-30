import JinWishartFormalization.MIMOWishartSER

/-!
# Exact SER/CDF identity for the actual shifted-Gram model

The theorem below states the BPSK Gaussian-Q average in terms of the actual
sample-space CDF. It is an identity for the SER plus its nonnegative
complement-CDF correction; it does not identify that CDF with the paper's
determinant formula.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

variable {m n : ℕ}

theorem standardNormalDensity_nonneg (t : ℝ) : 0 ≤ standardNormalDensity t := by
  unfold standardNormalDensity
  positivity

theorem gaussianQ_nonneg (x : ℝ) : 0 ≤ gaussianQ x := by
  unfold gaussianQ
  exact setIntegral_nonneg measurableSet_Ioi fun t _ => standardNormalDensity_nonneg t

theorem gaussianQ_antitone : Antitone gaussianQ := by
  intro x y hxy
  unfold gaussianQ
  apply setIntegral_mono_set
  · exact integrable_standardNormalDensity.integrableOn
  · exact ae_of_all _ fun t => standardNormalDensity_nonneg t
  · exact (Ioi_subset_Ioi hxy).eventuallyLE

theorem measurable_gaussianQ : Measurable gaussianQ :=
  gaussianQ_antitone.measurable

/-- For the actual shifted complex Gaussian Gram channel, BPSK average SER
plus the CDF-complement kernel integral is exactly `1/2`. Here `beta` is the
SNR scale, so the Q argument is `sqrt (2 * beta * lambda_min)`. Taking
`m = 2`, `n = 1` gives the two-row, one-column case. -/
theorem noncentralGram_BPSK_SER_add_cdfComplementIntegral
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (∫⁻ z, ENNReal.ofReal
        (gaussianQ (Real.sqrt
          (2 * beta * noncentralGramLeastEigenvalue M hn z)))
        ∂stdGaussian (ComplexSample (m := m) (n := n))) +
      ∫⁻ t in Ioi 0,
        (1 - noncentralGramScaledLeastEigenvalueCDF M hn beta t) *
          ENNReal.ofReal (gaussianQKernel t) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  let f : ComplexSample (m := m) (n := n) → ℝ :=
    fun z => 2 * beta * noncentralGramLeastEigenvalue M hn z
  have hf_meas : Measurable f := by
    dsimp [f, noncentralGramLeastEigenvalue]
    exact measurable_const.mul (measurable_complexNoncentralSampleSmallestEigenvalue M hn)
  have hq_meas : Measurable fun z => gaussianQ (Real.sqrt (f z)) :=
    measurable_gaussianQ.comp (Real.continuous_sqrt.measurable.comp hf_meas)
  have hpoint : ∀ z, ENNReal.ofReal (gaussianQ (Real.sqrt (f z))) +
      ENNReal.ofReal (gaussianQ 0 - gaussianQ (Real.sqrt (f z))) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
    intro z
    rw [← ENNReal.ofReal_add (gaussianQ_nonneg _)
      (sub_nonneg.mpr (gaussianQ_antitone (Real.sqrt_nonneg (f z))))]
    rw [gaussianQ_zero]
    ring_nf
  rw [← noncentralGram_meanGaussianQDecrement_eq_cdfComplementIntegral M hn beta hbeta]
  change (∫⁻ z, ENNReal.ofReal (gaussianQ (Real.sqrt (f z)))
        ∂stdGaussian (ComplexSample (m := m) (n := n))) +
      (∫⁻ z, ENNReal.ofReal (gaussianQ 0 - gaussianQ (Real.sqrt (f z)))
        ∂stdGaussian (ComplexSample (m := m) (n := n))) = _
  rw [← lintegral_add_left
    (f := fun z => ENNReal.ofReal (gaussianQ (Real.sqrt (f z))))
    (ENNReal.measurable_ofReal.comp hq_meas)]
  simp_rw [hpoint]
  simp

end JinWishart
