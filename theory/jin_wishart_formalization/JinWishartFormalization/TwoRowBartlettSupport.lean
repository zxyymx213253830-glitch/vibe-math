import JinWishartFormalization.TwoRowRandomDirectionLaw
import JinWishartFormalization.TwoRowGramSupport
import JinWishartFormalization.DeepSeekHour20261010.GammaZeroBoundary

/-!
# Actual positive Bartlett support

Codex support direction, paired with local DeepSeek's density direction.
The first singleton-null lemma is reused unchanged from the local model.
Existing 200000-sample fixed-seed actual Bartlett controls were checked first.
[需人工审查] Measure transport and interpretation as the paper's sample model.
This module does not assume or establish a spectral or Gram density.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart

theorem twoRow_firstEnergy_nonpositive_null :
    (gammaMeasure 2 1) (Set.Iic 0) = 0 := by
  rw [← measure_congr (Iio_ae_eq_Iic' deepseek_hour_GammaZeroBoundary)]
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem twoRow_residualEnergy_zero_null :
    (expMeasure 1) ({0} : Set ℝ) = 0 := by
  simp [expMeasure, gammaMeasure]

theorem twoRow_residualEnergy_nonpositive_null :
    (expMeasure 1) (Set.Iic 0) = 0 := by
  rw [← measure_congr (Iio_ae_eq_Iic' twoRow_residualEnergy_zero_null)]
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem twoRow_Bartlett_product_positive_ae :
    ∀ᵐ p ∂(gammaMeasure 2 1).prod
      (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1)),
      0 < p.1 ∧ 0 < p.2.2 := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hs : ∀ᵐ s ∂gammaMeasure 2 1, 0 < s := by
    rw [ae_iff]
    simpa only [not_lt, Set.Iic_def] using twoRow_firstEnergy_nonpositive_null
  have he : ∀ᵐ e ∂expMeasure 1, 0 < e := by
    rw [ae_iff]
    simpa only [not_lt, Set.Iic_def] using twoRow_residualEnergy_nonpositive_null
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hs] with s hs
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  exact ae_of_all _ fun _ => he.mono fun _ he => ⟨hs, he⟩

theorem actualTwoRow_Bartlett_positive_ae :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := 2) (n := 2)),
      0 < (twoRowBartlettCoordinates z).1 ∧
        0 < (twoRowBartlettCoordinates z).2.2 := by
  have h := twoRow_Bartlett_product_positive_ae
  rw [← actualTwoRow_BartlettCoordinates_law] at h
  exact ae_of_ae_map measurable_twoRowBartlettCoordinates.aemeasurable h

theorem actualTwoRow_Bartlett_nonpositive_null :
    (stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | ¬(0 < (twoRowBartlettCoordinates z).1 ∧
        0 < (twoRowBartlettCoordinates z).2.2)} = 0 := by
  exact ae_iff.mp actualTwoRow_Bartlett_positive_ae

end JinWishart

#print axioms JinWishart.twoRow_firstEnergy_nonpositive_null
#print axioms JinWishart.twoRow_residualEnergy_zero_null
#print axioms JinWishart.twoRow_residualEnergy_nonpositive_null
#print axioms JinWishart.twoRow_Bartlett_product_positive_ae
#print axioms JinWishart.actualTwoRow_Bartlett_positive_ae
#print axioms JinWishart.actualTwoRow_Bartlett_nonpositive_null
