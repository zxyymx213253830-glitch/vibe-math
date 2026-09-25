import JinWishartFormalization.NoncentralScalarCDF
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter MeasureTheory Set Topology

namespace JinWishart

/-- The order `(1,0)` Rice/Nuttall tail at zero amplitude reduces to the
ordinary Gaussian radial tail. -/
theorem nuttallQ_10_zeroAmplitude_eq_exp (b : ℝ) (hb : 0 ≤ b) :
    nuttallQ 1 0 0 b = (Real.exp (-(b ^ 2 / 2)) : ℂ) := by
  rw [nuttallQ_10_zeroAmplitude_eq_realIntegral]
  have hderiv : ∀ t ∈ Ici b,
      HasDerivAt (fun u : ℝ ↦ -Real.exp (-(u ^ 2 / 2)))
        (t * Real.exp (-(t ^ 2 / 2))) t := by
    intro t _
    have hinner : HasDerivAt (fun u : ℝ ↦ -(u ^ 2 / 2)) (-t) t := by
      convert (((hasDerivAt_id t).pow 2).div_const 2).neg using 1
      · funext u
        simp [Function.comp_def, id]
      · simp [id]
    convert ((Real.hasDerivAt_exp (-(t ^ 2 / 2))).comp t hinner).neg using 1
    · funext u
      simp [Function.comp_def, id] <;> ring
    · simp [id] <;> ring
  have hbase : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(t ^ 2 / 2))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (s := (1 : ℝ)) (by norm_num) (by norm_num)
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 h
    intro t ht
    change t * Real.exp (-(t ^ 2 / 2)) = Real.rpow t (1 : ℝ) * Real.exp (-(1 / 2) * t ^ 2)
    calc
      t * Real.exp (-(t ^ 2 / 2)) = t * Real.exp (-(1 / 2) * t ^ 2) := by
        congr 1 <;> ring_nf
      _ = Real.rpow t (1 : ℝ) * Real.exp (-(1 / 2) * t ^ 2) := by
        exact congrArg (fun z : ℝ => z * Real.exp (-(1 / 2) * t ^ 2))
          (Real.rpow_one t).symm
  have hint : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(t ^ 2 / 2))) (Ioi b) :=
    hbase.mono_set (Ioi_subset_Ioi hb)
  have hsq : Tendsto (fun t : ℝ ↦ t ^ 2) atTop atTop := by
    refine tendsto_atTop.2 fun c ↦ ?_
    filter_upwards [eventually_ge_atTop (max c 1)] with t ht
    have ht1 : 1 ≤ t := (le_max_right c 1).trans ht
    have htc : c ≤ t := (le_max_left c 1).trans ht
    nlinarith [sq_nonneg t]
  have hlim : Tendsto (fun t : ℝ ↦ -Real.exp (-(t ^ 2 / 2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      0 (1 / 2 : ℝ) (by norm_num)).comp hsq
    have h' : Tendsto (fun t : ℝ ↦ Real.exp (-(t ^ 2 / 2))) atTop (𝓝 0) := by
      convert h using 1
      funext t
      simp only [Function.comp_apply, Real.rpow_zero, one_mul]
      congr 1
      ring
    simpa using h'.neg
  have htail := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have hreal : (∫ t in Ioi b, t * Real.exp (-(t ^ 2 / 2))) =
      Real.exp (-(b ^ 2 / 2)) := by
    simpa using htail
  rw [hreal]

end JinWishart
