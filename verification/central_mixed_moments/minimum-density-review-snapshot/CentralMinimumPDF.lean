import JinWishartFormalization.CentralMinimumActualDensity
import Mathlib.Probability.Density

/-! Public PDF API for the actual general central minimum law.
Codex. [需人工审查] Inherited FTC/measure/variance/model interpretation.
The result is a one-dimensional marginal, not joint spectral density G2. -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def actualCentralMinimumDensity (d n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal (centralMinimumPDFCore d n x))

theorem measurable_actualCentralMinimumDensity (d n : ℕ) :
    Measurable (actualCentralMinimumDensity d n) := by
  exact ((continuous_centralMinimumPDFCore d n).measurable.ennreal_ofReal).indicator measurableSet_Ioi

theorem lintegral_actualCentralMinimumDensity (d n : ℕ) :
    (∫⁻ x, actualCentralMinimumDensity d n x)=1 := by
  have h := congrArg (fun μ : Measure ℝ => μ Set.univ) (actualCentralMinimum_map_eq_density d n)
  rw [measure_univ,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ] at h
  exact h.symm

instance actualCentralMinimum_hasPDF (d n : ℕ) :
    HasPDF (centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n))
      (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))) volume := by
  exact hasPDF_of_map_eq_withDensity (measurable_centralGaussianSampleMinimum _ _ _).aemeasurable
    (actualCentralMinimumDensity d n) (measurable_actualCentralMinimumDensity d n).aemeasurable
    (actualCentralMinimum_map_eq_density d n)

theorem pdf_actualCentralMinimum_eq (d n : ℕ) :
    pdf (centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n))
      (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))) volume =ᵐ[volume]
      actualCentralMinimumDensity d n := by
  rw [pdf_def,actualCentralMinimum_map_eq_density]
  exact Measure.rnDeriv_withDensity volume (measurable_actualCentralMinimumDensity d n)

end
end JinWishart
#print axioms JinWishart.measurable_actualCentralMinimumDensity
#print axioms JinWishart.lintegral_actualCentralMinimumDensity
#print axioms JinWishart.actualCentralMinimum_hasPDF
#print axioms JinWishart.pdf_actualCentralMinimum_eq
