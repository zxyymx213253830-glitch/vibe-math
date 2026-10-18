import JinWishartFormalization.CentralWishartClosedDensity
import JinWishartFormalization.CentralWishartConeIntegral

/-!
# Actual central square Wishart strict minimum law, every positive size

Codex: actual matrix density followed by translation of the positive cone.
No eigenvalue joint density is assumed. The trace-translation dependency retains
its original local DeepSeek GUIDED_COLLABORATION provenance.
[需人工审查] Cone events, nonnegative integrals, spectral and variance conventions.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem measurableSet_centralCoordinatePositiveCone (n : ℕ) :
    MeasurableSet (centralCoordinatePositiveCone n) :=
  (measurableSet_complex_posDef n).preimage continuous_hermitianOfRealCoordinates.measurable

theorem measurableSet_centralCoordinateShiftedCone (n : ℕ) (x : ℝ) :
    MeasurableSet (centralCoordinateShiftedCone n x) := by
  apply (measurableSet_complex_posDef n).preimage
  exact (continuous_hermitianOfRealCoordinates.sub continuous_const).measurable

theorem centralCoordinateShiftedCone_subset_positive (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    centralCoordinateShiftedCone n x ⊆ centralCoordinatePositiveCone n := by
  intro q hq
  change (hermitianOfRealCoordinates q - (x : ℂ) • 1).PosDef at hq
  have hs : ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosSemidef.diagonal (fun _ => by
      change (0 : ℂ) ≤ (x : ℂ)
      exact_mod_cast hx)
  have h := hq.add_posSemidef hs
  change (hermitianOfRealCoordinates q).PosDef
  simpa only [sub_add_cancel] using h

theorem centralWishartCoordinateDensity_on_cone (d n : ℕ)
    (q : Matrix (Fin n) (Fin n) ℝ) (hq : q ∈ centralCoordinatePositiveCone n) :
    centralWishartCoordinateDensity d n q = ENNReal.ofReal (centralWishartDensityConstant d n) *
      ENNReal.ofReal (centralConeWeight d (hermitianOfRealCoordinates q)) := by
  classical
  change (hermitianOfRealCoordinates q).PosDef at hq
  rw [centralWishartCoordinateDensity, if_pos hq,
    ← ENNReal.ofReal_mul (centralWishartDensityConstant_pos d n).le]
  simp only [centralConeWeight, mul_assoc]

theorem centralWishartCoordinateDensity_cone_mass (d n : ℕ) :
    ENNReal.ofReal (centralWishartDensityConstant d n) *
      (∫⁻ q in centralCoordinatePositiveCone n,
        ENNReal.ofReal (centralConeWeight d (hermitianOfRealCoordinates q))
          ∂hermitianRealCoordinateMeasure n) = 1 := by
  rw [← lintegral_centralWishartCoordinateDensity d n,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator (measurableSet_centralCoordinatePositiveCone n)]
  apply lintegral_congr
  intro q
  by_cases hq : q ∈ centralCoordinatePositiveCone n
  · rw [Set.indicator_of_mem hq, centralWishartCoordinateDensity_on_cone d n q hq]
  · rw [Set.indicator_of_notMem hq]
    symm
    exact if_neg hq

/-- An actual probability identity in every rectangular central dimension.
For t>s the determinant polynomial is retained; no exponential-only shortcut. -/
theorem actualCentralWishart_shiftedCone_probability (d n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ((complexWishart (m := d + n) (n := n)).map realCoordinatesOfHermitian)
      (centralCoordinateShiftedCone n x) =
      ENNReal.ofReal (centralWishartDensityConstant d n) *
        ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) *
          (∫⁻ q in centralCoordinatePositiveCone n,
            ENNReal.ofReal ((hermitianOfRealCoordinates q + (x : ℂ) • 1).det.re ^ d *
              Real.exp (-(hermitianOfRealCoordinates q).trace.re))
                ∂hermitianRealCoordinateMeasure n) := by
  rw [complexWishart_realCoordinates_eq_closedDensity,
    withDensity_apply _ (measurableSet_centralCoordinateShiftedCone n x)]
  have he : (∫⁻ q in centralCoordinateShiftedCone n x, centralWishartCoordinateDensity d n q
      ∂hermitianRealCoordinateMeasure n) =
      ENNReal.ofReal (centralWishartDensityConstant d n) *
        (∫⁻ q in centralCoordinateShiftedCone n x,
          ENNReal.ofReal (centralConeWeight d (hermitianOfRealCoordinates q))
            ∂hermitianRealCoordinateMeasure n) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun (measurableSet_centralCoordinateShiftedCone n x)
    intro q hq
    exact centralWishartCoordinateDensity_on_cone d n q
      (centralCoordinateShiftedCone_subset_positive n x hx hq)
  rw [he, centralCone_candidateIntegral_shift, mul_assoc]

theorem actualCentralSquareWishart_shiftedCone_probability (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian)
      (centralCoordinateShiftedCone n x) = ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) := by
  have h := actualCentralWishart_shiftedCone_probability 0 n x hx
  simp only [Nat.zero_add, pow_zero, one_mul] at h
  rw [h, mul_right_comm,
    show (∫⁻ q in centralCoordinatePositiveCone n,
      ENNReal.ofReal (Real.exp (-(hermitianOfRealCoordinates q).trace.re))
        ∂hermitianRealCoordinateMeasure n) =
      ∫⁻ q in centralCoordinatePositiveCone n,
        ENNReal.ofReal (centralConeWeight 0 (hermitianOfRealCoordinates q))
          ∂hermitianRealCoordinateMeasure n by simp [centralConeWeight],
    centralWishartCoordinateDensity_cone_mass, one_mul]

def centralSquareSampleMinimum (n : ℕ) (hn : 0 < n)
    (z : ComplexSample (m := n) (n := n)) : ℝ :=
  complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin n) (Fin n) ℂ) hn z

theorem measurable_centralSquareSampleMinimum (n : ℕ) (hn : 0 < n) :
    Measurable (centralSquareSampleMinimum n hn) :=
  measurable_complexNoncentralSampleSmallestEigenvalue _ _

theorem centralSquareSampleMinimum_threshold (n : ℕ) (hn : 0 < n)
    (z : ComplexSample (m := n) (n := n)) (x : ℝ) :
    realCoordinatesOfHermitian (complexSampleGram z) ∈ centralCoordinateShiftedCone n x ↔
      x < centralSquareSampleMinimum n hn z := by
  have hG := (complexGram_posSemidef (complexSampleMatrix z)).isHermitian
  change (hermitianOfRealCoordinates (realCoordinatesOfHermitian
    (complexGram (complexSampleMatrix z))) - (x : ℂ) • 1).PosDef ↔ _
  rw [hermitianOfRealCoordinates_realCoordinates _ hG,
    hermitian_shift_posDef_iff_smallest _ hG hn x]
  simp only [centralSquareSampleMinimum, complexNoncentralSampleSmallestEigenvalue, add_zero]

/-- All positive square sizes: the actual strict minimum survival probability. -/
theorem actualCentralSquare_minimum_tail (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (ComplexSample (m := n) (n := n)))
      {z | x < centralSquareSampleMinimum n hn z} =
        ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) := by
  have h := actualCentralSquareWishart_shiftedCone_probability n x hx
  rw [complexWishart,
    Measure.map_map continuous_realCoordinatesOfHermitian.measurable measurable_complexSampleGram,
    Measure.map_apply
      (continuous_realCoordinatesOfHermitian.measurable.comp measurable_complexSampleGram)
      (measurableSet_centralCoordinateShiftedCone n x)] at h
  have he : (realCoordinatesOfHermitian ∘ complexSampleGram) ⁻¹'
      centralCoordinateShiftedCone n x = {z | x < centralSquareSampleMinimum n hn z} := by
    ext z
    exact centralSquareSampleMinimum_threshold n hn z x
  rw [he] at h
  exact h

theorem actualCentralSquare_minimum_CDF (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := n) (n := n)))
      {z | centralSquareSampleMinimum n hn z ≤ x}).toReal =
        1 - Real.exp (-(n : ℝ) * x) := by
  have hs : MeasurableSet {z | x < centralSquareSampleMinimum n hn z} :=
    measurableSet_lt measurable_const (measurable_centralSquareSampleMinimum n hn)
  have hc := probReal_add_probReal_compl
    (μ := stdGaussian (ComplexSample (m := n) (n := n))) hs
  have he : {z | x < centralSquareSampleMinimum n hn z}ᶜ =
      {z | centralSquareSampleMinimum n hn z ≤ x} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rw [he] at hc
  simp only [Measure.real] at hc
  rw [actualCentralSquare_minimum_tail n hn x hx,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hc
  linarith only [hc]

theorem centralSquareSampleMinimum_nonneg (n : ℕ) (hn : 0 < n)
    (z : ComplexSample (m := n) (n := n)) : 0 ≤ centralSquareSampleMinimum n hn z :=
  complexNoncentralGram_eigenvalues₀_nonneg _ _ _

theorem actualCentralSquare_minimum_cdf_function (n : ℕ) (hn : 0 < n) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := n) (n := n))).map
      (centralSquareSampleMinimum n hn)) x =
        if 0 ≤ x then 1 - Real.exp (-(n : ℝ) * x) else 0 := by
  rw [cdf_eq_real, Measure.real,
    Measure.map_apply (measurable_centralSquareSampleMinimum n hn) measurableSet_Iic]
  change ((stdGaussian (ComplexSample (m := n) (n := n)))
    {z | centralSquareSampleMinimum n hn z ≤ x}).toReal = _
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact actualCentralSquare_minimum_CDF n hn x hx
  · rw [if_neg hx]
    have he : {z : ComplexSample (m := n) (n := n) |
        centralSquareSampleMinimum n hn z ≤ x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hx)
        (centralSquareSampleMinimum_nonneg n hn z)) hz
    simp [he]

/-- General square central minimum law: Exp(rate n) for every n>0. -/
theorem actualCentralSquare_minimum_law_exp (n : ℕ) (hn : 0 < n) :
    (stdGaussian (ComplexSample (m := n) (n := n))).map (centralSquareSampleMinimum n hn) =
      expMeasure (n : ℝ) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have : IsProbabilityMeasure (expMeasure (n : ℝ)) := isProbabilityMeasure_expMeasure hnr
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro x
  rw [actualCentralSquare_minimum_cdf_function, cdf_expMeasure_eq hnr]
  simp only [neg_mul]

end
end JinWishart

#print axioms JinWishart.measurableSet_centralCoordinatePositiveCone
#print axioms JinWishart.measurableSet_centralCoordinateShiftedCone
#print axioms JinWishart.centralCoordinateShiftedCone_subset_positive
#print axioms JinWishart.centralWishartCoordinateDensity_on_cone
#print axioms JinWishart.centralWishartCoordinateDensity_cone_mass
#print axioms JinWishart.actualCentralWishart_shiftedCone_probability
#print axioms JinWishart.actualCentralSquareWishart_shiftedCone_probability
#print axioms JinWishart.measurable_centralSquareSampleMinimum
#print axioms JinWishart.centralSquareSampleMinimum_threshold
#print axioms JinWishart.actualCentralSquare_minimum_tail
#print axioms JinWishart.actualCentralSquare_minimum_CDF
#print axioms JinWishart.centralSquareSampleMinimum_nonneg
#print axioms JinWishart.actualCentralSquare_minimum_cdf_function
#print axioms JinWishart.actualCentralSquare_minimum_law_exp
