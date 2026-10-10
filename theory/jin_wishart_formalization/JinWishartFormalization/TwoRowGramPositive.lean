import JinWishartFormalization.TwoRowBartlettSupport

/-!
# Actual central two-row Gram determinant support

Codex support direction. Uses actual Bartlett positivity, including the local
DeepSeek singleton-null lemma. No density is assumed.
[需人工审查] Interpretation of this actual central 2x2 support in paper notation.
-/

open MeasureTheory ProbabilityTheory

namespace JinWishart

theorem twoRowBartlettGram_det (p : ℝ × (ℂ × ℝ)) (hs : 0 ≤ p.1) :
    (twoRowBartlettGram p).det = (p.1 * p.2.2 : ℝ) := by
  have hr : (Real.sqrt p.1 : ℂ) ^ 2 = (p.1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt hs
  have hz : p.2.1 * star p.2.1 = (‖p.2.1‖ ^ 2 : ℝ) := by
    simpa only [starRingEnd_apply, Complex.ofReal_pow] using Complex.mul_conj' p.2.1
  simp [Matrix.det_fin_two, twoRowBartlettGram, star_mul, RCLike.star_def]
  calc
    _ = (p.1 : ℂ) * ((‖p.2.1‖ ^ 2 : ℝ) + p.2.2) -
        (Real.sqrt p.1 : ℂ) ^ 2 * (p.2.1 * star p.2.1) := by
          simp only [Complex.ofReal_pow, starRingEnd_apply]
          ring
    _ = (p.1 : ℂ) * p.2.2 := by rw [hr, hz]; ring

theorem actualTwoRow_Gram_eq_BartlettGram
    (z : ComplexSample (m := 2) (n := 2)) :
    complexGram (complexSampleMatrix z) = twoRowBartlettGram (twoRowBartlettCoordinates z) := by
  unfold twoRowBartlettCoordinates
  rw [← twoRowGramFromCoordinates_eq_BartlettGram]
  simpa only [Prod.mk.eta, twoColumnJoin_split] using
    twoRow_actualGram_reconstruction (twoColumnSplit z).1 (twoColumnSplit z).2

theorem actualTwoRow_Gram_det_positive_ae :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := 2) (n := 2)),
      0 < (complexGram (complexSampleMatrix z)).det.re := by
  filter_upwards [actualTwoRow_Bartlett_positive_ae] with z hz
  rw [actualTwoRow_Gram_eq_BartlettGram,
    twoRowBartlettGram_det _ hz.1.le, Complex.ofReal_re]
  exact mul_pos hz.1 hz.2

theorem actualTwoRow_Gram_det_zero_null :
    (stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | (complexGram (complexSampleMatrix z)).det = 0} = 0 := by
  apply measure_mono_null (t := {z | ¬0 < (complexGram (complexSampleMatrix z)).det.re})
    (fun z hz => ?_) (ae_iff.mp actualTwoRow_Gram_det_positive_ae)
  change (complexGram (complexSampleMatrix z)).det = 0 at hz
  change ¬0 < (complexGram (complexSampleMatrix z)).det.re
  simp [hz]

end JinWishart

#print axioms JinWishart.twoRowBartlettGram_det
#print axioms JinWishart.actualTwoRow_Gram_eq_BartlettGram
#print axioms JinWishart.actualTwoRow_Gram_det_positive_ae
#print axioms JinWishart.actualTwoRow_Gram_det_zero_null
