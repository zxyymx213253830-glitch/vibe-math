import JinWishartFormalization.GaussianComplexOrthogonalResidual
import JinWishartFormalization.GaussianRadialCDF

/-!
# Exact residual energy for the minimal genuine two-column Gram model

An explicit orthogonal partner in complex dimension two identifies residual
energy with a scalar complex Gaussian energy. Reuse the existing exponential
law, rather than proving radial integration again.
[需人工审查] Partner/conjugation convention and actual variance normalization.
-/

open MeasureTheory ProbabilityTheory

namespace JinWishart

noncomputable section

def complexTwoRowPartner (a : ComplexColumnSpace 2) : ComplexColumnSpace 2 :=
  WithLp.toLp 2 (fun i => if i = 0 then -star (a 1) else star (a 0))

theorem complexTwoRowPartner_norm (a : ComplexColumnSpace 2) :
    ‖complexTwoRowPartner a‖ = ‖a‖ := by
  have hs : ‖complexTwoRowPartner a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp [complexTwoRowPartner, Fin.sum_univ_two, add_comm]
  nlinarith [norm_nonneg (complexTwoRowPartner a), norm_nonneg a]

theorem complexTwoRowPartner_residual (a z : ComplexColumnSpace 2) (ha : ‖a‖ = 1) :
    complexOrthogonalResidual a z = (inner ℂ (complexTwoRowPartner a) z) •
      complexTwoRowPartner a := by
  have hc : a 0 * star (a 0) + a 1 * star (a 1) = 1 := by
    have h : inner ℂ a a = 1 := by
      rw [inner_self_eq_norm_sq_to_K, ha]
      norm_num
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      starRingEnd_apply, Pi.star_apply] using h
  ext i
  fin_cases i
  · simp [complexOrthogonalResidual_apply, complexTwoRowPartner,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    simp only [starRingEnd_apply] at hc ⊢
    linear_combination -(z 0) * hc
  · simp [complexOrthogonalResidual_apply, complexTwoRowPartner,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    simp only [starRingEnd_apply] at hc ⊢
    linear_combination -(z 1) * hc

theorem complexTwoRow_residualEnergy_eq_projection (a z : ComplexColumnSpace 2)
    (ha : ‖a‖ = 1) :
    ‖complexOrthogonalResidual a z‖ ^ 2 = ‖inner ℂ (complexTwoRowPartner a) z‖ ^ 2 := by
  rw [complexTwoRowPartner_residual a z ha, norm_smul, complexTwoRowPartner_norm, ha, mul_one]

theorem complexGaussianEnergy_law :
    (stdGaussian ℂ).map complexGaussianEnergy = expMeasure 1 := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  exact cdf_complexGaussianEnergy_eq_expMeasure

theorem complexGaussian_scaled_energy (z : ℂ) :
    ‖(Real.sqrt 2)⁻¹ • z‖ ^ 2 = complexGaussianEnergy z := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt 2)⁻¹)]
  unfold complexGaussianEnergy
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  nlinarith

/-- The residual from an actual two-row complex Gaussian column has Exp(1) energy. -/
theorem actualTwoRow_residualEnergy_law (a : ComplexColumnSpace 2) (ha : ‖a‖ = 1) :
    (stdGaussian (TwoColumnBlock 2)).map
      (fun v => ‖complexOrthogonalResidual a (actualComplexColumn v)‖ ^ 2) =
      expMeasure 1 := by
  simp_rw [complexTwoRow_residualEnergy_eq_projection a _ ha]
  have hm : Measurable (fun v : TwoColumnBlock 2 =>
      inner ℂ (complexTwoRowPartner a) (actualComplexColumn v)) :=
    (innerSL ℂ (complexTwoRowPartner a)).continuous.measurable.comp
      (by unfold actualComplexColumn; fun_prop)
  calc
    _ = ((stdGaussian (TwoColumnBlock 2)).map
        (fun v => inner ℂ (complexTwoRowPartner a) (actualComplexColumn v))).map
        (fun w : ℂ => ‖w‖ ^ 2) := by
      rw [Measure.map_map (by fun_prop) hm]
      rfl
    _ = ((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).map
        (fun w : ℂ => ‖w‖ ^ 2) := by
      rw [actualComplexColumn_inner_law, complexTwoRowPartner_norm, ha, mul_one]
    _ = expMeasure 1 := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      simpa only [Function.comp_def, complexGaussian_scaled_energy] using complexGaussianEnergy_law

/-- The actual complex projection and residual energy have their product law. -/
theorem actualTwoRow_projection_residualEnergy_joint_law
    (a : ComplexColumnSpace 2) (ha : ‖a‖ = 1) :
    (stdGaussian (TwoColumnBlock 2)).map
      (fun v => (inner ℂ a (actualComplexColumn v),
        ‖complexOrthogonalResidual a (actualComplexColumn v)‖ ^ 2)) =
      ((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1) := by
  have hm : Measurable (actualComplexColumn (m := 2)) := by
    unfold actualComplexColumn
    fun_prop
  have hf : Measurable (fun v : TwoColumnBlock 2 => inner ℂ a (actualComplexColumn v)) :=
    (innerSL ℂ a).continuous.measurable.comp hm
  have hg : Measurable (fun v : TwoColumnBlock 2 =>
      ‖complexOrthogonalResidual a (actualComplexColumn v)‖ ^ 2) := by
    fun_prop
  rw [(actualComplexColumn_projection_indep_residualEnergy a ha).map_prod_eq_prod_map_map
      hf.aemeasurable hg.aemeasurable, actualComplexColumn_inner_law, ha, mul_one,
    actualTwoRow_residualEnergy_law a ha]

end

end JinWishart
