import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Exponential
import JinWishartFormalization.GaussianRadialLaw
import JinWishartFormalization.RadialIntegration
import JinWishartFormalization.Theorem1Formula

open MeasureTheory Set ProbabilityTheory
open intervalIntegral
open scoped ENNReal

namespace JinWishart

noncomputable def complexGaussianEnergy (z : ℂ) : ℝ := ‖z‖ ^ 2 / 2

@[fun_prop]
theorem measurable_complexGaussianEnergy : Measurable complexGaussianEnergy := by
  unfold complexGaussianEnergy
  fun_prop

private noncomputable def complexGaussianRadialPDF (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2)

private theorem integrable_complexGaussianRadialPDF :
    Integrable (fun z : ℂ ↦ complexGaussianRadialPDF ‖z‖) volume := by
  have h₁ : IntegrableOn (fun r : ℝ ↦ r * complexGaussianRadialPDF r) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (s := (1 : ℝ)) (by norm_num) (by norm_num)
    have h' := h.const_mul ((2 * Real.pi)⁻¹)
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 h'
    intro r hr
    simp only [complexGaussianRadialPDF]
    rw [show -(r ^ 2) / 2 = -(1 / 2) * r ^ 2 by ring]
    rw [Real.rpow_one]
    ring
  exact (integrable_fun_norm_addHaar (μ := (volume : Measure ℂ))
    (f := complexGaussianRadialPDF)).2 (by
      simpa [Complex.finrank_real_complex, complexGaussianRadialPDF,
        pow_one, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h₁)

private theorem integral_radiusGaussian (R : ℝ) (hR : 0 ≤ R) :
    ∫ r in Ioc (0 : ℝ) R, r * complexGaussianRadialPDF r =
      (2 * Real.pi)⁻¹ * (1 - Real.exp (-(R ^ 2) / 2)) := by
  rw [← integral_of_le hR]
  have hderiv : ∀ u ∈ Icc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ ↦ -Real.exp (-(t ^ 2) / 2))
        (u * Real.exp (-(u ^ 2) / 2)) u := by
    intro u hu
    have hinner : HasDerivAt (fun t : ℝ ↦ -(t ^ 2) / 2) (-u) u := by
      convert (((hasDerivAt_id u).pow 2).div_const 2).neg using 1
      · funext t
        simp [Function.comp_def, id]
        ring
      · simp [id]
    convert ((Real.hasDerivAt_exp (-(u ^ 2) / 2)).comp u hinner).neg using 1
    · funext t
      simp [Function.comp_def, id]
    · simp [id]
      ring
  have hint : IntervalIntegrable (fun r : ℝ ↦ r * Real.exp (-(r ^ 2) / 2))
      volume 0 R := by
    exact (show Continuous (fun r : ℝ ↦ r * Real.exp (-(r ^ 2) / 2)) by fun_prop)
      |>.intervalIntegrable 0 R
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (by fun_prop) (fun u hu ↦ hderiv u (Ioo_subset_Icc_self hu)) hint
  have hfun : (fun r : ℝ ↦ r * complexGaussianRadialPDF r) =
      (fun r ↦ (2 * Real.pi)⁻¹ * (r * Real.exp (-(r ^ 2) / 2))) := by
    funext r
    simp [complexGaussianRadialPDF]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, hFTC]
  simp [complexGaussianRadialPDF]
  <;> ring

private theorem integral_complex_radial_closedBall (R : ℝ) (f : ℝ → ℝ) :
    ∫ z in Metric.closedBall (0 : ℂ) R, f ‖z‖ ∂volume =
      2 * Real.pi * ∫ r in Ioc (0 : ℝ) R, r * f r := by
  let g : ℝ → ℝ := (Iic R).indicator f
  have hfun : (fun z : ℂ ↦ g ‖z‖) =
      (Metric.closedBall (0 : ℂ) R).indicator (fun z ↦ f ‖z‖) := by
    funext z
    simp [g, Set.indicator, Metric.closedBall, dist_eq_norm]
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
  rw [← hfun, integral_complex_radial]
  rw [show (fun r : ℝ ↦ r * g r) = (Iic R).indicator (fun r ↦ r * f r) by
    funext r
    by_cases hr : r ≤ R <;> simp [g, hr]]
  rw [MeasureTheory.integral_indicator measurableSet_Iic]
  rw [Measure.restrict_restrict measurableSet_Iic]
  rw [inter_comm]
  rw [show Ioi (0 : ℝ) ∩ Iic R = Ioc 0 R by ext r; simp]

theorem stdGaussian_complex_closedBall (R : ℝ) (hR : 0 ≤ R) :
    (stdGaussian ℂ) (Metric.closedBall (0 : ℂ) R) =
      ENNReal.ofReal (1 - Real.exp (-(R ^ 2) / 2)) := by
  have hballInt :
      ∫ z in Metric.closedBall (0 : ℂ) R, complexGaussianRadialPDF ‖z‖ =
        1 - Real.exp (-(R ^ 2) / 2) := by
    rw [integral_complex_radial_closedBall, integral_radiusGaussian R hR]
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    field_simp [hpi]
  rw [stdGaussian_complex_eq_radialDensity,
    withDensity_apply _ measurableSet_closedBall]
  have hInt : Integrable (fun z : ℂ ↦ complexGaussianRadialPDF ‖z‖)
      (volume.restrict (Metric.closedBall (0 : ℂ) R)) :=
    integrable_complexGaussianRadialPDF.restrict
  have hnonneg : 0 ≤ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) R)]
      (fun z : ℂ ↦ complexGaussianRadialPDF ‖z‖) :=
    ae_of_all _ fun z ↦ by
      unfold complexGaussianRadialPDF
      positivity
  change (∫⁻ z in Metric.closedBall (0 : ℂ) R,
    ENNReal.ofReal (complexGaussianRadialPDF ‖z‖) ∂volume) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
  simpa [complexGaussianRadialPDF] using congrArg ENNReal.ofReal hballInt

theorem complexGaussianEnergy_measure_Iic (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian ℂ).map complexGaussianEnergy (Iic x) =
      ENNReal.ofReal (1 - Real.exp (-x)) := by
  rw [Measure.map_apply measurable_complexGaussianEnergy measurableSet_Iic]
  have hevent : complexGaussianEnergy ⁻¹' Iic x =
      Metric.closedBall (0 : ℂ) (Real.sqrt (2 * x)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, Metric.mem_closedBall,
      dist_zero_right, complexGaussianEnergy]
    constructor
    · intro hz
      have hs : Real.sqrt (2 * x) ^ 2 = 2 * x :=
        Real.sq_sqrt (by positivity)
      have hn : ‖z‖ ^ 2 ≤ Real.sqrt (2 * x) ^ 2 := by nlinarith [hz, hs]
      by_contra hnot
      have hlt : Real.sqrt (2 * x) < ‖z‖ := lt_of_not_ge hnot
      have hsum : 0 < ‖z‖ + Real.sqrt (2 * x) := by
        nlinarith [Real.sqrt_nonneg (2 * x)]
      have hprod := mul_pos (sub_pos.mpr hlt) hsum
      nlinarith
    · intro hz
      have hs : Real.sqrt (2 * x) ^ 2 = 2 * x :=
        Real.sq_sqrt (by positivity)
      have hprod := mul_nonneg (sub_nonneg.mpr hz)
        (add_nonneg (norm_nonneg z) (Real.sqrt_nonneg (2 * x)))
      nlinarith
  rw [hevent, stdGaussian_complex_closedBall _ (Real.sqrt_nonneg _)]
  have hs : Real.sqrt (2 * x) ^ 2 = 2 * x := Real.sq_sqrt (by positivity)
  rw [hs]
  congr 1
  ring

theorem cdf_complexGaussianEnergy_eq_expMeasure (x : ℝ) :
    cdf ((stdGaussian ℂ).map complexGaussianEnergy) x = cdf (expMeasure 1) x := by
  haveI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  by_cases hx : 0 ≤ x
  · have hmass := complexGaussianEnergy_measure_Iic x hx
    have hformula := cdf_expMeasure_eq (r := 1) (by norm_num) x
    have hnonneg₁ := cdf_nonneg ((stdGaussian ℂ).map complexGaussianEnergy) x
    have hnonneg₂ := cdf_nonneg (expMeasure 1) x
    apply (ENNReal.ofReal_eq_ofReal_iff hnonneg₁ hnonneg₂).mp
    calc
      ENNReal.ofReal (cdf ((stdGaussian ℂ).map complexGaussianEnergy) x) =
          ((stdGaussian ℂ).map complexGaussianEnergy) (Iic x) := ofReal_cdf _ _
      _ = ENNReal.ofReal (1 - Real.exp (-x)) := hmass
      _ = ENNReal.ofReal (cdf (expMeasure 1) x) := by
        rw [hformula]
        simp [hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hpre : complexGaussianEnergy ⁻¹' Iic x = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false]
      constructor
      · intro hz
        have hE : 0 ≤ complexGaussianEnergy z := by
          unfold complexGaussianEnergy
          positivity
        linarith
      · intro hfalse
        exact False.elim hfalse
    have hzero : ((stdGaussian ℂ).map complexGaussianEnergy) (Iic x) = 0 := by
      rw [Measure.map_apply measurable_complexGaussianEnergy measurableSet_Iic, hpre]
      simp
    rw [cdf_eq_real, cdf_expMeasure_eq (r := 1) (by norm_num), if_neg hx]
    simp [measureReal_def, hzero]

/-- The radial energy of a single central complex-Gaussian sample has the
unit-rate exponential law. This is the scalar `1 × 1` Wishart distribution
result, not the matrix-valued density theorem of the paper. -/
theorem centralScalarSampleEnergy_map_eq_expMeasure :
    (stdGaussian (ComplexSample (m := 1) (n := 1))).map centralScalarSampleEnergy =
      expMeasure 1 := by
  rw [centralScalarSampleEnergy_map_eq_radialGaussianEnergy]
  haveI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro x
  exact cdf_complexGaussianEnergy_eq_expMeasure x

/-- Consequently, the least eigenvalue of the `1 × 1` central complex Gram
sample is exponential. -/
theorem centralScalarSmallestEigenvalue_map_eq_expMeasure :
    (stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (by norm_num)) = expMeasure 1 := by
  have hfun :
      complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (by norm_num) = centralScalarSampleEnergy := by
    funext x
    exact centralScalarSampleSmallestEigenvalue_eq_energy x
  rw [hfun, centralScalarSampleEnergy_map_eq_expMeasure]

/-- The actual largest-eigenvalue event of the central `1 × 1` Wishart law is
the exponential sublevel event. This uses the weak CDF event (`≤`), so it does
not rely on exchanging strict and weak probabilities by an unproved
atomlessness claim. -/
theorem centralScalarLargestEigenvalueCdf_eq_expMeasure (x : ℝ) :
    complexNoncentralWishartLargestEigenvalueCdf
        (m := 1) (n := 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) x =
      expMeasure 1 (Iic x) := by
  rw [complexNoncentralWishartLargestEigenvalueCdf, complexNoncentralWishart]
  rw [Measure.map_apply (measurable_shiftedComplexSampleGram (M :=
    (0 : Matrix (Fin 1) (Fin 1) ℂ))) (measurableSet_largestEigenvalueCdfEvent x)]
  have hpre :
      (fun y : ComplexSample (m := 1) (n := 1) ↦
        complexGram (complexSampleMatrix y + (0 : Matrix (Fin 1) (Fin 1) ℂ))) ⁻¹'
          largestEigenvalueCdfEvent x =
        centralScalarSampleEnergy ⁻¹' Iic x := by
    ext y
    let hW := (complexGram_posSemidef (complexSampleMatrix y)).1
    have hidx : smallestEigenvalue₀Index (n := 1) (by norm_num) =
        (⟨0, by norm_num⟩ : Fin (Fintype.card (Fin 1))) := by
      apply Fin.ext
      simp [smallestEigenvalue₀Index]
    have hmin : hW.eigenvalues₀
        (smallestEigenvalue₀Index (n := 1) (by norm_num)) =
        centralScalarSampleEnergy y := by
      simpa [hW, complexNoncentralSampleSmallestEigenvalue, add_zero] using
        centralScalarSampleSmallestEigenvalue_eq_energy y
    have hmax : hW.eigenvalues₀ (⟨0, by norm_num⟩ : Fin (Fintype.card (Fin 1))) =
        centralScalarSampleEnergy y := by
      rw [← hidx]
      exact hmin
    simp only [Set.mem_preimage]
    simp only [add_zero]
    change complexGram (complexSampleMatrix y) ∈ largestEigenvalueCdfEvent x ↔
      centralScalarSampleEnergy y ∈ Iic x
    rw [largestEigenvalueCdfEvent_iff_largest_eigenvalue₀_le
      _ hW (by norm_num) x]
    simp only [add_zero, hmax, Set.mem_preimage, Set.mem_Iic]
  rw [hpre]
  have hfun : centralScalarSampleEnergy =
      complexGaussianEnergy ∘ centralScalarToComplex := by
    funext y
    exact centralScalarEnergy_eq_complexNorm y
  have hmeas : Measurable centralScalarSampleEnergy := by
    rw [hfun]
    exact measurable_complexGaussianEnergy.comp centralScalarToComplex.continuous.measurable
  rw [← Measure.map_apply hmeas measurableSet_Iic,
    centralScalarSampleEnergy_map_eq_expMeasure]

/-- The CDF in the one-sample central scalar specialization of the paper's
formula is now identified with the actual Gaussian sample's weakest eigenvalue
CDF. -/
theorem theorem1CentralScalarOneSample_eq_sampleSmallestEigenvalueCDF
    (x : ℝ) (hx : 0 ≤ x) :
    theorem1CdfCandidate 1 1 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x =
      cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (by norm_num))) x := by
  rw [theorem1CentralScalarOneSample_eq_exponentialCDF x hx,
    centralScalarSmallestEigenvalue_map_eq_expMeasure]

/-- Theorem 2's one-dimensional central specialization reduces to the same
unit-rate exponential CDF. In dimension one, the largest and smallest
eigenvalues coincide. -/
theorem theorem2CentralScalarOneSample_eq_exponentialCDF (x : ℝ) (hx : 0 ≤ x) :
    theorem2CdfCandidate 1 1 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x = cdf (expMeasure 1) x := by
  rw [theorem2CdfCandidate]
  rw [cdf_expMeasure_eq (r := 1) (by norm_num) x]
  simp [theorem2XiMatrix, theorem2XiEntry, theorem1PsiMatrix,
    theorem1PsiEntry, theorem1GammaIndex, upperGammaNat_zero,
    partialGamma_one, hx]
  have hnonneg : 0 ≤ 1 - Real.exp (-x) := by
    have he : Real.exp (-x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    linarith
  rw [show (1 : ℂ) - Complex.exp (-(x : ℂ)) =
      ((1 - Real.exp (-x) : ℝ) : ℂ) by push_cast; simp]
  rw [Complex.norm_of_nonneg hnonneg]

/-- Theorem 2's central scalar formula equals the probability of the actual
largest-eigenvalue weak-CDF event under the `1 × 1` complex Wishart model. -/
theorem theorem2CentralScalarOneSample_eq_largestEigenvalueEvent
    (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal
        (theorem2CdfCandidate 1 1 0 (by omega) (by omega)
          (fun j : Fin 0 => Fin.elim0 j) x) =
      complexNoncentralWishartLargestEigenvalueCdf
        (m := 1) (n := 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) x := by
  haveI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  rw [theorem2CentralScalarOneSample_eq_exponentialCDF x hx]
  calc
    ENNReal.ofReal (cdf (expMeasure 1) x) = expMeasure 1 (Iic x) :=
      ofReal_cdf _ _
    _ = complexNoncentralWishartLargestEigenvalueCdf
        (m := 1) (n := 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) x :=
      (centralScalarLargestEigenvalueCdf_eq_expMeasure x).symm

end JinWishart
