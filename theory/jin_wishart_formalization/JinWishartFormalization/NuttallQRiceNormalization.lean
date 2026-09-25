import JinWishartFormalization.ScalarNoncentralCDFRice
import JinWishartFormalization.NuttallQRiceMass
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Total mass of the Rice radial kernel

This identifies the total Rice mass by sending the finite-radius scalar
noncentral CDF formula to infinity.  The only analytic input beyond the
finite-radius formula is integrability of the Rice kernel on `(0, ∞)`.
-/

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology

namespace JinWishart

noncomputable section

/-- The Rice radial kernel has unit total mass for every nonnegative
noncentrality amplitude. -/
theorem riceRadialKernel_integral_eq_one (a : ℝ) (ha : 0 ≤ a) :
    (∫ r in Ioi (0 : ℝ), riceRadialKernel a r) = 1 := by
  let M : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => ((a / Real.sqrt 2 : ℝ) : ℂ)
  have hmean : ‖complexSampleMean M‖ = a := by
    rw [← scalarComplexMean_norm_eq_sampleMean_norm]
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    simp only [M, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt,
      abs_of_nonneg (div_nonneg ha hsqrt.le)]
    field_simp
    <;> ring
  have hint : IntegrableOn (riceRadialKernel a) (Ioi 0) :=
    riceRadialKernel_integrableOn_Ioi a ha
  have hRadialLimit :
      Tendsto (fun n : ℕ => ∫ r in (0 : ℝ)..(n : ℝ), riceRadialKernel a r)
        atTop (𝓝 (∫ r in Ioi (0 : ℝ), riceRadialKernel a r)) := by
    exact intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop
  let μ := (stdGaussian (ComplexSample (m := 1) (n := 1))).map
    (complexNoncentralSampleSmallestEigenvalue M (by norm_num))
  have hCDF : Tendsto (cdf μ) atTop (𝓝 1) := tendsto_cdf_atTop μ
  have hxlim : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / 2) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
    filter_upwards [Filter.eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
    have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hCDFseq : Tendsto (fun n : ℕ => cdf μ ((n : ℝ) ^ 2 / 2))
      atTop (𝓝 1) := hCDF.comp hxlim
  have hseq : ∀ n : ℕ,
      (∫ r in (0 : ℝ)..(n : ℝ), riceRadialKernel a r) =
        cdf μ ((n : ℝ) ^ 2 / 2) := by
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfinite := noncentralScalarCDF_eq_riceRadialIntegral M
      ((n : ℝ) ^ 2 / 2) (by positivity)
    have hsqrt : Real.sqrt (2 * ((n : ℝ) ^ 2 / 2)) = n := by
      rw [show 2 * ((n : ℝ) ^ 2 / 2) = (n : ℝ) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hn]
    rw [hsqrt] at hfinite
    rw [← intervalIntegral.integral_of_le hn] at hfinite
    simpa [μ, hmean] using hfinite.symm
  have hRadialSeq : Tendsto
      (fun n : ℕ => ∫ r in (0 : ℝ)..(n : ℝ), riceRadialKernel a r)
      atTop (𝓝 (∫ r in Ioi (0 : ℝ), riceRadialKernel a r)) := hRadialLimit
  have hCDFSeq' : Tendsto
      (fun n : ℕ => ∫ r in (0 : ℝ)..(n : ℝ), riceRadialKernel a r)
      atTop (𝓝 1) := hCDFseq.congr (fun n => (hseq n).symm)
  have heq := tendsto_nhds_unique hRadialSeq hCDFSeq'
  exact heq

end

end JinWishart
