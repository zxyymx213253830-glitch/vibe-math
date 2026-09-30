import JinWishartFormalization.NoncentralSixDimensionalRadial
import JinWishartFormalization.ThreeRowSampleCoordinates
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Total mass of the actual three-row radial kernel

The finite-radius probability identity for the actual complex `3 × 1`
sample, together with integrability of the independently derived E₆ radial
kernel, identifies its total mass by taking integer radii to infinity.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace JinWishart

noncomputable section

/-- The actual arbitrary-mean three-row CDF converges to the total mass of
the six-dimensional radial kernel along integer radii. -/
theorem noncentralChiSixRadialSeriesKernel_integral_eq_one (a : ℝ) :
    (∫ r in Ioi (0 : ℝ), noncentralChiSixRadialSeriesKernel a r) = 1 := by
  have hint : IntegrableOn (noncentralChiSixRadialSeriesKernel a) (Ioi 0) :=
    integrableOn_noncentralChiSixRadialSeriesKernel a
  have hRadialLimit :
      Tendsto (fun n : ℕ => ∫ r in (0 : ℝ)..(n : ℝ),
        noncentralChiSixRadialSeriesKernel a r) atTop
        (𝓝 (∫ r in Ioi (0 : ℝ), noncentralChiSixRadialSeriesKernel a r)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop
  let M : Matrix (Fin 3) (Fin 1) ℂ := threeRowAxialMean a
  have hmean : ‖threeRowSampleToFin6 (complexSampleMean M)‖ = |a| := by
    change ‖threeRowSampleToFin6
      (complexSampleMean (threeRowAxialMean a))‖ = |a|
    rw [threeRowSampleToFin6_complexSampleMean]
    rw [norm_smul, EuclideanSpace.norm_single]
    norm_num [Real.norm_eq_abs]
  let μ := (stdGaussian (ComplexSample (m := 3) (n := 1))).map
    (complexNoncentralSampleSmallestEigenvalue M (by norm_num))
  have hCDF : Tendsto (cdf μ) atTop (𝓝 1) := tendsto_cdf_atTop μ
  have hxlim : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / 2) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
    filter_upwards [Filter.eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
    have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hCDFseq : Tendsto (fun n : ℕ => cdf μ ((n : ℝ) ^ 2 / 2)) atTop (𝓝 1) :=
    hCDF.comp hxlim
  have hseq : ∀ n : ℕ,
      (∫ r in (0 : ℝ)..(n : ℝ), noncentralChiSixRadialSeriesKernel a r) =
        cdf μ ((n : ℝ) ^ 2 / 2) := by
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfinite := noncentralThreeRowCDF_eq_radialSeries_of_mean M
      ((n : ℝ) ^ 2 / 2) (by positivity)
    have hsqrt : Real.sqrt (2 * ((n : ℝ) ^ 2 / 2)) = n := by
      rw [show 2 * ((n : ℝ) ^ 2 / 2) = (n : ℝ) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hn]
    rw [hsqrt, hmean] at hfinite
    rw [← intervalIntegral.integral_of_le hn] at hfinite
    simpa [μ] using hfinite.symm
  have hCDFSeq' : Tendsto
      (fun n : ℕ => ∫ r in (0 : ℝ)..(n : ℝ),
        noncentralChiSixRadialSeriesKernel a r) atTop (𝓝 1) :=
    hCDFseq.congr (fun n => (hseq n).symm)
  exact tendsto_nhds_unique hRadialLimit hCDFSeq'

end

end JinWishart
