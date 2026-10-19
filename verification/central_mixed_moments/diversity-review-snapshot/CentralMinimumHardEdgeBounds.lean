import JinWishartFormalization.CentralMinimumGammaSandwich
import JinWishartFormalization.GammaHardEdgeBounds
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# General central minimum: explicit hard-edge power bounds

Codex proofs. These prove the diversity ORDER, not the sharp T4 coefficient.
[需人工审查] Actual CDF event interpretation and asymptotic filter.
-/
open Filter MeasureTheory ProbabilityTheory Asymptotics
open scoped Topology
namespace JinWishart
noncomputable section

def actualCentralMinimumCDF (d n : ℕ) (x : ℝ) : ℝ :=
  (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
    {z | centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n) z ≤ x}

theorem actualCentralMinimumCDF_power_bounds (d n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x)*x^(d+1)/(Nat.factorial (d+1) : ℝ) ≤ actualCentralMinimumCDF d n x ∧
    actualCentralMinimumCDF d n x ≤ ((n+1 : ℕ) : ℝ)^(d+2)*x^(d+1)/(Nat.factorial (d+1) : ℝ) := by
  have hs := actualCentral_minimum_gamma_sandwich d n hn x
  refine ⟨(cdf_gammaMeasure_nat_power_lower d x hx).trans hs.1,?_⟩
  have hupper := mul_le_mul_of_nonneg_left
    (cdf_gammaMeasure_nat_power_upper d (((n+1 : ℕ) : ℝ)*x) (mul_nonneg (Nat.cast_nonneg _) hx))
    (Nat.cast_nonneg (n+1) : (0 : ℝ) ≤ (n+1 : ℕ))
  apply hs.2.trans
  apply hupper.trans_eq
  simp only [mul_pow,show d+2=(d+1)+1 by omega,pow_succ]
  ring

theorem actualCentralMinimumCDF_local_power_bounds (d n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (Real.exp (-1)/(Nat.factorial (d+1) : ℝ))*x^(d+1) ≤ actualCentralMinimumCDF d n x ∧
    actualCentralMinimumCDF d n x ≤
      (((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ))*x^(d+1) := by
  have h := actualCentralMinimumCDF_power_bounds d n hn x hx.le
  constructor
  · apply le_trans _ h.1
    have he := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hx1))
      (show 0 ≤ x^(d+1)/(Nat.factorial (d+1) : ℝ) from
        div_nonneg (pow_nonneg hx.le _) (Nat.cast_nonneg _))
    simpa only [div_mul_eq_mul_div,mul_div_assoc] using he
  · simpa only [div_mul_eq_mul_div] using h.2

theorem actualCentralMinimumCDF_isTheta_power (d n : ℕ) (hn : 0 < n) :
    (fun x : ℝ => actualCentralMinimumCDF d n x) =Θ[𝓝[>] 0] (fun x => x^(d+1)) := by
  let c : ℝ := Real.exp (-1)/(Nat.factorial (d+1) : ℝ)
  let C : ℝ := ((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hb : ∀ᶠ x : ℝ in 𝓝[>] 0,
      0 < x ∧ c*x^(d+1) ≤ actualCentralMinimumCDF d n x ∧ actualCentralMinimumCDF d n x ≤ C*x^(d+1) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx hx1
    exact ⟨hx,actualCentralMinimumCDF_local_power_bounds d n hn x hx hx1.le⟩
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hb] with x hx
    have hF : 0 ≤ actualCentralMinimumCDF d n x := ENNReal.toReal_nonneg
    simpa only [Real.norm_eq_abs,abs_of_nonneg hF,
      abs_of_nonneg (pow_nonneg hx.1.le _)] using hx.2.2
  · apply Asymptotics.IsBigO.of_bound c⁻¹
    filter_upwards [hb] with x hx
    have hF : 0 ≤ actualCentralMinimumCDF d n x := ENNReal.toReal_nonneg
    have h : x^(d+1) ≤ c⁻¹*actualCentralMinimumCDF d n x := by
      rw [← div_eq_inv_mul]
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hx.2.1
    simpa only [Real.norm_eq_abs,abs_of_nonneg hF,
      abs_of_nonneg (pow_nonneg hx.1.le _),div_eq_mul_inv,mul_comm] using h

end
end JinWishart
#print axioms JinWishart.actualCentralMinimumCDF_power_bounds
#print axioms JinWishart.actualCentralMinimumCDF_local_power_bounds
#print axioms JinWishart.actualCentralMinimumCDF_isTheta_power
