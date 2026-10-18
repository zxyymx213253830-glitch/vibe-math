import JinWishartFormalization.GramDeterminantPolynomial
import JinWishartFormalization.CentralWishartShiftedDeterminantMean

/-! Exact finite factorial-functional evaluation of every shifted determinant moment.
Codex proofs. [需人工审查] Bochner/lintegral correspondence and actual-law transport.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

def centralGaussianShiftedDeterminantMoment (d n : ℕ) (x : ℝ) : ℝ :=
  (complexGaussianPolynomialMoment (shiftedGramDeterminantPolynomial n n d x)).re

theorem shiftedGramDeterminant_power_real (m n d : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (z : ComplexSample (m := m) (n := n)) :
    (((complexSampleGram z+(x : ℂ) • 1).det.re^d : ℝ) : ℂ) =
      (complexSampleGram z+(x : ℂ) • 1).det^d := by
  have hI : ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hx)
  have hA := (complexGram_posSemidef (complexSampleMatrix z)).add hI
  have hi := (Complex.nonneg_iff.mp hA.det_nonneg).2
  rw [Complex.ofReal_pow]
  congr 1
  apply Complex.ext
  · simp
  · simpa only [complexSampleGram,Complex.ofReal_im] using hi

theorem integrable_actual_shiftedGramDeterminant_re_power (m n d : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    Integrable (fun z => (complexSampleGram z+(x : ℂ) • 1).det.re^d)
      (stdGaussian (ComplexSample (m := m) (n := n))) := by
  have h := (integrable_actual_shiftedGramDeterminant_power m n d x).re
  have he : (fun z : ComplexSample (m := m) (n := n) =>
      (complexSampleGram z+(x : ℂ) • 1).det.re^d) =
        fun z => ((complexSampleGram z+(x : ℂ) • 1).det^d).re := by
    funext z
    rw [← shiftedGramDeterminant_power_real m n d x hx z]
    norm_cast
  rw [he]
  exact h

theorem integral_actual_shiftedGramDeterminant_re_power (d n : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (∫ z, (complexSampleGram z+(x : ℂ) • 1).det.re^d
      ∂stdGaussian (ComplexSample (m := n) (n := n))) =
        centralGaussianShiftedDeterminantMoment d n x := by
  have he : (fun z : ComplexSample (m := n) (n := n) =>
      (complexSampleGram z+(x : ℂ) • 1).det.re^d) =
        fun z => ((complexSampleGram z+(x : ℂ) • 1).det^d).re := by
    funext z
    rw [← shiftedGramDeterminant_power_real n n d x hx z]
    norm_cast
  rw [he]
  calc
    _ = (∫ z, (complexSampleGram z+(x : ℂ) • 1).det^d
        ∂stdGaussian (ComplexSample (m := n) (n := n))).re := by
      exact integral_re (integrable_actual_shiftedGramDeterminant_power n n d x)
    _ = _ := congrArg Complex.re (integral_actual_shiftedGramDeterminant_power n n d x)

theorem centralGaussianShiftedDeterminantMoment_nonneg (d n : ℕ)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ centralGaussianShiftedDeterminantMoment d n x := by
  rw [← integral_actual_shiftedGramDeterminant_re_power d n x hx]
  apply integral_nonneg
  intro z
  have hI : ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hx)
  exact pow_nonneg (Complex.nonneg_iff.mp
    ((complexGram_posSemidef (complexSampleMatrix z)).add hI).det_nonneg).1 d

theorem lintegral_actualCentralSquare_shiftedDeterminant_power (d n : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ A, ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^d)
      ∂complexWishart (m := n) (n := n)) =
        ENNReal.ofReal (centralGaussianShiftedDeterminantMoment d n x) := by
  unfold complexWishart
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  rw [← integral_actual_shiftedGramDeterminant_re_power d n x hx,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_actual_shiftedGramDeterminant_re_power n n d x hx)]
  exact ae_of_all _ (fun z => by
    have hI : ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
      Matrix.PosSemidef.one.smul (by exact_mod_cast hx)
    exact pow_nonneg (Complex.nonneg_iff.mp
      ((complexGram_posSemidef (complexSampleMatrix z)).add hI).det_nonneg).1 d)

end
end JinWishart
#print axioms JinWishart.shiftedGramDeterminant_power_real
#print axioms JinWishart.integrable_actual_shiftedGramDeterminant_re_power
#print axioms JinWishart.integral_actual_shiftedGramDeterminant_re_power
#print axioms JinWishart.centralGaussianShiftedDeterminantMoment_nonneg
#print axioms JinWishart.lintegral_actualCentralSquare_shiftedDeterminant_power
