import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import JinWishartFormalization.WishartProbability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart

private theorem map_withDensity_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (hmp : MeasurePreserving e μ ν) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply f (hs.preimage e.measurable), withDensity_apply (f ∘ e.symm) hs]
  calc
    ∫⁻ x in e ⁻¹' s, f x ∂μ =
        ∫⁻ x in e ⁻¹' s, (f ∘ e.symm) (e x) ∂μ := by
          apply setLIntegral_congr_fun (hs.preimage e.measurable)
          intro x hx
          simp
    _ = ∫⁻ y in s, (f ∘ e.symm) y ∂ν := by
      exact hmp.setLIntegral_comp_preimage hs (hf.comp e.symm.measurable)

noncomputable def complexCoordinates : ℂ ≃ᵐ ℝ × ℝ :=
  Complex.measurableEquivPi.trans (MeasurableEquiv.piFinTwo fun _ : Fin 2 ↦ ℝ)

theorem measurePreserving_complexCoordinates :
    MeasurePreserving complexCoordinates volume (volume : Measure (ℝ × ℝ)) := by
  exact (volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℝ)).comp
    Complex.volume_preserving_equiv_pi

theorem stdGaussian_complex_eq_withDensity :
    stdGaussian ℂ = volume.withDensity
      (fun z : ℂ ↦ gaussianPDF 0 1 z.re * gaussianPDF 0 1 z.im) := by
  classical
  let μ : Measure ℝ := gaussianReal 0 1
  have hμ : μ = volume.withDensity (gaussianPDF 0 1) := by
    simpa [μ] using @gaussianReal_of_var_ne_zero 0 1 (by norm_num)
  let e := complexCoordinates
  let f : ℝ × ℝ → ℝ≥0∞ := fun p ↦ gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2
  have hprod : μ.prod μ = (volume : Measure (ℝ × ℝ)).withDensity f := by
    rw [hμ]
    simpa [f, ← Measure.volume_eq_prod ℝ ℝ] using (prod_withDensity (measurable_gaussianPDF 0 1)
      (measurable_gaussianPDF 0 1) :
        (volume.withDensity (gaussianPDF 0 1)).prod
          (volume.withDensity (gaussianPDF 0 1)) = _)
  have hmap : (Measure.pi fun _ : Fin 2 ↦ μ).map
      (MeasurableEquiv.piFinTwo fun _ : Fin 2 ↦ ℝ) = μ.prod μ :=
    (measurePreserving_piFinTwo (fun _ ↦ μ)).map_eq
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI]
  have hcoord : (fun x : Fin 2 → ℝ ↦ ∑ i, x i • Complex.orthonormalBasisOneI i) =
      e.symm ∘ (MeasurableEquiv.piFinTwo fun _ : Fin 2 ↦ ℝ) := by
    funext x
    simp [e, complexCoordinates, Complex.measurableEquivPi_symm_apply,
      Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two]
  rw [hcoord, ← Measure.map_map]
  · rw [hmap, hprod]
    have hmp := measurePreserving_complexCoordinates.symm
    rw [map_withDensity_measurePreserving e.symm (volume : Measure (ℝ × ℝ)) volume
      hmp f (by fun_prop)]
    simp [e, complexCoordinates, f, Function.comp_def,
      Complex.measurableEquivPi_apply]
  · exact e.symm.measurable
  · exact (MeasurableEquiv.piFinTwo fun _ : Fin 2 ↦ ℝ).measurable

theorem gaussianPDF_complex_coordinates_eq_radial (z : ℂ) :
    gaussianPDF 0 1 z.re * gaussianPDF 0 1 z.im =
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-(‖z‖ ^ 2) / 2)) := by
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul
    (gaussianPDFReal_nonneg 0 1 z.re)]
  simp only [gaussianPDFReal_def]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hnorm : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa [pow_two] using (RCLike.norm_sq_eq_def (z := z)).symm
  congr 1
  simp only [sub_zero, NNReal.coe_one]
  have hden : Real.sqrt (2 * Real.pi * (1 : ℝ)) = Real.sqrt (2 * Real.pi) := by simp
  rw [hden]
  ring_nf
  rw [mul_assoc, ← Real.exp_add]
  rw [show z.re ^ 2 * (-1 / 2) + z.im ^ 2 * (-1 / 2) = ‖z‖ ^ 2 * (-1 / 2) by
    rw [← hnorm]
    ring]
  field_simp [hsqrt, Real.pi_ne_zero]
  rw [Real.sq_sqrt (by positivity : 0 ≤ Real.pi * 2)]

theorem stdGaussian_complex_eq_radialDensity :
    stdGaussian ℂ = volume.withDensity
      (fun z : ℂ ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-(‖z‖ ^ 2) / 2))) := by
  rw [stdGaussian_complex_eq_withDensity]
  congr 1
  funext z
  exact gaussianPDF_complex_coordinates_eq_radial z

noncomputable def centralScalarIndexEquiv :
    ((Fin 1 × Fin 1) × Fin 2) ≃ Fin 2 where
  toFun := Prod.snd
  invFun i := ((0, 0), i)
  left_inv := by
    rintro ⟨⟨i, j⟩, k⟩
    fin_cases i
    fin_cases j
    rfl
  right_inv := by intro i; rfl

noncomputable def centralScalarToComplex :
    ComplexSample (m := 1) (n := 1) ≃ₗᵢ[ℝ] ℂ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ centralScalarIndexEquiv).trans
    Complex.orthonormalBasisOneI.repr.symm

theorem stdGaussian_map_centralScalarToComplex :
    (stdGaussian (ComplexSample (m := 1) (n := 1))).map centralScalarToComplex =
      stdGaussian ℂ :=
  stdGaussian_map centralScalarToComplex

theorem centralScalarEnergy_eq_complexNorm
    (x : ComplexSample (m := 1) (n := 1)) :
    centralScalarSampleEnergy x = ‖centralScalarToComplex x‖ ^ 2 / 2 := by
  have hcoord : centralScalarToComplex x =
      (x ((0, 0), 0) : ℂ) + (x ((0, 0), 1) : ℂ) * Complex.I := by
    simp [centralScalarToComplex, centralScalarIndexEquiv,
      LinearIsometryEquiv.piLpCongrLeft_apply,
      Complex.orthonormalBasisOneI_repr_symm_apply, Equiv.piCongrLeft']
  rw [hcoord]
  rw [RCLike.norm_sq_eq_def]
  simp [centralScalarSampleEnergy, Complex.add_re, Complex.mul_re]
  ring

theorem centralScalarSampleEnergy_map_eq_radialGaussianEnergy :
    (stdGaussian (ComplexSample (m := 1) (n := 1))).map centralScalarSampleEnergy =
      (stdGaussian ℂ).map (fun z : ℂ ↦ ‖z‖ ^ 2 / 2) := by
  have hfun : centralScalarSampleEnergy =
      (fun z : ℂ ↦ ‖z‖ ^ 2 / 2) ∘ centralScalarToComplex := by
    funext x
    exact centralScalarEnergy_eq_complexNorm x
  rw [hfun, ← Measure.map_map, stdGaussian_map_centralScalarToComplex]
  all_goals fun_prop

end JinWishart
