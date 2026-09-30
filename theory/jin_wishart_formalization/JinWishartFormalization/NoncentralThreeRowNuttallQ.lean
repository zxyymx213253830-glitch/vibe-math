import JinWishartFormalization.NoncentralSixDimensionalMass
import Mathlib.Probability.CDF

/-!
# The actual three-row CDF as a normalized Nuttall-Q tail

The finite-radius CDF is already identified with the actual six-dimensional
radial kernel.  This module complements that lower mass to the unit total mass
and replaces the upper radial kernel by the proved `(3,2)` Nuttall-Q integrand.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

/-- For nonzero axial displacement, the lower radial mass is one minus the
upper tail written directly with the normalized `(3,2)` Nuttall integrand. -/
theorem noncentralChiSixRadialSeriesKernel_lowerMass_eq_one_sub_nuttallQ32Integral
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 ≤ b) :
    (∫ r in Ioc (0 : ℝ) b, noncentralChiSixRadialSeriesKernel a r) =
      1 - ∫ r in Ioi b,
        (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2).re := by
  have hpoint (r : ℝ) :
      noncentralChiSixRadialSeriesKernel a r =
        (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2).re := by
    have h := noncentralChiSixRadialSeriesKernel_eq_nuttallQ32_div_sq a r ha
    simpa using congrArg Complex.re h
  have htotal : (∫ r : ℝ, noncentralChiSixRadialSeriesKernel a r
      ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ))) = 1 := by
    simpa only [] using noncentralChiSixRadialSeriesKernel_integral_eq_one a
  have hupper : Ioi (0 : ℝ) ∩ Ioi b = Ioi b := by
    ext r
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro hr
      exact ⟨lt_of_le_of_lt hb hr, hr⟩
  have hlower : Ioi (0 : ℝ) ∩ (Ioi b)ᶜ = Ioc (0 : ℝ) b := by
    ext r
    simp [mem_inter_iff, mem_Ioi, mem_compl_iff, mem_Ioc]
  have hpart := setIntegral_compl (μ := (volume : Measure ℝ).restrict
      (Ioi (0 : ℝ))) (s := Ioi b) measurableSet_Ioi
      (integrableOn_noncentralChiSixRadialSeriesKernel a)
  have htailRestrict :
      (∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r
        ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ))) =
        (∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r) := by
    change (∫ r, noncentralChiSixRadialSeriesKernel a r
      ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).restrict (Ioi b)) = _
    rw [Measure.restrict_restrict measurableSet_Ioi, Set.inter_comm, hupper]
  have htailQ :
      (∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r) =
        (∫ r in Ioi b,
          (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2).re) := by
    apply integral_congr_ae
    filter_upwards with r
    exact hpoint r
  have hlowerRestrict :
      (∫ r in (Ioi b)ᶜ, noncentralChiSixRadialSeriesKernel a r
        ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ))) =
        (∫ r in Ioc (0 : ℝ) b, noncentralChiSixRadialSeriesKernel a r) := by
    change (∫ r, noncentralChiSixRadialSeriesKernel a r
      ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).restrict (Ioi b)ᶜ) = _
    rw [Measure.restrict_restrict measurableSet_Ioi.compl, Set.inter_comm, hlower]
  calc
    _ = ∫ r in (Ioi b)ᶜ, noncentralChiSixRadialSeriesKernel a r
        ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)) := hlowerRestrict.symm
    _ = 1 - ∫ r in Ioi b,
          (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2).re := by
      rw [hpart, htotal, htailRestrict, htailQ]

/-- Actual arbitrary-mean `3 × 1` least-eigenvalue CDF, expressed as one minus
the normalized order-`(3,2)` Nuttall tail. The amplitude is the norm of the
actual encoded complex mean, so it is nonnegative and the explicit nonzero
assumption is exactly what permits division by its square. -/
theorem noncentralThreeRowCDF_eq_one_sub_nuttallQ32Tail_of_mean
    (M : Matrix (Fin 3) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x)
    (ha : ‖threeRowSampleToFin6 (complexSampleMean M)‖ ≠ 0) :
    cdf ((stdGaussian (ComplexSample (m := 3) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      1 - ∫ r in Ioi (Real.sqrt (2 * x)),
        (nuttallQIntegrand 3 2
          ‖threeRowSampleToFin6 (complexSampleMean M)‖ r /
          (‖threeRowSampleToFin6 (complexSampleMean M)‖ : ℂ) ^ 2).re := by
  rw [noncentralThreeRowCDF_eq_radialSeries_of_mean M x hx]
  exact noncentralChiSixRadialSeriesKernel_lowerMass_eq_one_sub_nuttallQ32Integral
    _ _ ha (Real.sqrt_nonneg _)

/-- Axial-mean specialization of the actual three-row CDF/Nuttall-Q identity.
The signed axial parameter is allowed; the radial law itself is even in it. -/
theorem noncentralThreeRowAxialCDF_eq_one_sub_nuttallQ32Tail
    (a x : ℝ) (hx : 0 ≤ x) (ha : a ≠ 0) :
    cdf ((stdGaussian (ComplexSample (m := 3) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (threeRowAxialMean a) (by norm_num))) x =
      1 - ∫ r in Ioi (Real.sqrt (2 * x)),
        (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2).re := by
  rw [noncentralThreeRowAxialCDF_eq_radialSeries a x hx]
  exact noncentralChiSixRadialSeriesKernel_lowerMass_eq_one_sub_nuttallQ32Integral
    a (Real.sqrt (2 * x)) ha (Real.sqrt_nonneg _)

end

end JinWishart
