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

/-- The product density of finitely many independent standard real Gaussians
collapses to a radial expression. This is the density identity underlying the
higher-dimensional `stdGaussian` calculation. -/
theorem gaussianPDF_fintype_prod_eq_radial {ι : Type*} [Fintype ι]
    (x : ι → ℝ) :
    (∏ i, gaussianPDF 0 1 (x i)) =
      ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
          Real.exp (-(∑ i, x i ^ 2) / 2)) := by
  simp_rw [gaussianPDF_def, gaussianPDFReal_def]
  simp only [sub_zero, NNReal.coe_one]
  simp only [mul_one, div_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
    (f := fun i ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x i) ^ 2 / 2))]
  · congr 1
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 1
    · simp
    · apply congrArg Real.exp
      calc
        (∑ i, (-(x i) ^ 2 / 2)) = -((∑ i, (x i) ^ 2 / 2)) := by
          simp_rw [neg_div]
          rw [Finset.sum_neg_distrib]
        _ = -((∑ i, (x i) ^ 2) / 2) := by rw [Finset.sum_div]
        _ = (-(∑ i, (x i) ^ 2)) / 2 := by ring
  · intro i hi
    positivity

/-- The finite product of standard real Gaussian measures is the Lebesgue
measure weighted by the product of the one-dimensional PDFs. The proof checks
measurable rectangles and uses mathlib's finite-product Fubini theorem. -/
theorem pi_gaussianReal_eq_withDensity_fintype {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι ↦ gaussianReal 0 1) =
      volume.withDensity (fun x : ι → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hrect : MeasurableSet (Set.univ.pi s) := MeasurableSet.pi
    Set.countable_univ (fun i hi ↦ hs i)
  rw [withDensity_apply _ hrect, ← lintegral_indicator hrect]
  have hpoint :
      (Set.univ.pi s).indicator (fun x : ι → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i)) =
        fun x ↦ ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · have hxi : ∀ i, x i ∈ s i := by simpa using hx
      simp only [Set.indicator_of_mem hx, gaussianPDF_def]
      rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
        (f := fun i ↦ gaussianPDFReal 0 1 (x i))]
      · congr 1
        apply Finset.prod_congr rfl
        intro i hi
        symm
        exact Set.indicator_of_mem (hxi i) (gaussianPDFReal 0 1)
      · intro i hi
        exact gaussianPDFReal_nonneg 0 1 _
    · obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        by_contra h
        push_neg at h
        exact hx (by simpa using h)
      simp [Set.indicator, hx, hi, Finset.prod_eq_zero (Finset.mem_univ i)]
  rw [hpoint]
  have hint : Integrable
      (fun x : ι → ℝ ↦ ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i))
      (volume : Measure (ι → ℝ)) := by
    rw [volume_pi]
    apply Integrable.fintype_prod
    intro i
    exact Integrable.indicator (integrable_gaussianPDFReal 0 1) (hs i)
  have hnonneg : 0 ≤ᵐ[volume]
      (fun x : ι → ℝ ↦ ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) :=
    ae_of_all _ fun x ↦ Finset.prod_nonneg fun i hi ↦ by
      by_cases hx : x i ∈ s i
      · simpa [Set.indicator, hx] using gaussianPDFReal_nonneg 0 1 (x i)
      · simp [Set.indicator, hx]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  calc
    ENNReal.ofReal (∫ x : ι → ℝ,
        ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i) ∂volume) =
      ∏ i, ENNReal.ofReal (∫ x in s i, gaussianPDFReal 0 1 x) := by
        rw [integral_fintype_prod_volume_eq_prod]
        rw [ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
          (f := fun i ↦ ∫ x, (s i).indicator (gaussianPDFReal 0 1) x)]
        · simp_rw [integral_indicator (hs _)]
        · intro i hi
          exact integral_nonneg_of_ae (ae_of_all _ fun x ↦ by
            by_cases hx : x ∈ s i <;> simp [Set.indicator, hx, gaussianPDFReal_nonneg])
    _ = ∏ i, gaussianReal 0 1 (s i) := by
      apply Finset.prod_congr rfl
      intro i hi
      symm
      have hgauss : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
        gaussianReal_of_var_ne_zero 0 (v := 1) (by norm_num)
      rw [hgauss, withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
      have hInt := Integrable.indicator (integrable_gaussianPDFReal 0 1) (hs i)
      have hnn : 0 ≤ᵐ[volume] (s i).indicator (gaussianPDFReal 0 1) :=
        ae_of_all _ fun x ↦ by
          by_cases hx : x ∈ s i <;> simp [Set.indicator, hx, gaussianPDFReal_nonneg]
      have hfun : (s i).indicator (gaussianPDF 0 1) =
          fun x ↦ ENNReal.ofReal ((s i).indicator (gaussianPDFReal 0 1) x) := by
        funext x
        by_cases hx : x ∈ s i <;> simp [Set.indicator, hx, gaussianPDF_def]
      rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hInt hnn,
        integral_indicator (hs i)]

/-- The standard Gaussian on a finite-dimensional Euclidean coordinate space
has the product-PDF density with respect to its canonical Lebesgue measure. -/
theorem stdGaussian_euclidean_eq_productDensity {ι : Type*} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) = volume.withDensity
      (fun x : EuclideanSpace ℝ ι ↦ ∏ i, gaussianPDF 0 1 (x i)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity_fintype]
  let e : (ι → ℝ) ≃ᵐ EuclideanSpace ℝ ι := MeasurableEquiv.toLp 2 _
  have hmp : MeasurePreserving e (volume : Measure (ι → ℝ))
      (volume : Measure (EuclideanSpace ℝ ι)) := PiLp.volume_preserving_toLp ι
  change Measure.map e ((volume : Measure (ι → ℝ)).withDensity
    (fun x : ι → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i))) = _
  rw [map_withDensity_measurePreserving e volume volume hmp
    (fun x : ι → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i)) (by fun_prop)]
  congr 1

/-- In Euclidean coordinates, the finite product of standard Gaussian PDFs is
radial, giving an explicit density depending only on the norm. -/
theorem stdGaussian_euclidean_eq_radialDensity {ι : Type*} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) = volume.withDensity
      (fun x : EuclideanSpace ℝ ι ↦ ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
          Real.exp (-(‖x‖ ^ 2) / 2))) := by
  rw [stdGaussian_euclidean_eq_productDensity]
  congr 1
  funext x
  rw [gaussianPDF_fintype_prod_eq_radial]
  congr 1
  rw [← EuclideanSpace.real_norm_sq_eq]

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
