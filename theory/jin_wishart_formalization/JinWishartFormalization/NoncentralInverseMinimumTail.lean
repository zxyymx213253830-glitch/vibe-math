import JinWishartFormalization.NoncentralMinimumDiversity
import JinWishartFormalization.GaussianGramFullRank

/-!
# Reciprocal minimum-eigenvalue tail of the actual fixed-mean model

Codex. Zero inverse at0 is handled by the actual almost-sure full-rank theorem.
This is a tail exponent; an inverse-moment integrability criterion is NOT yet proved.
[需人工审查] Null-set/event transport and reciprocal-tail interpretation.
-/
open Matrix Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualNoncentral_minimum_pos_ae {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      0 < complexNoncentralSampleSmallestEigenvalue M hn z := by
  classical
  filter_upwards [complexSample_shiftedGram_posDef_ae hnm M] with z hz
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have h := hz.eigenvalues_pos (e (smallestEigenvalue₀Index hn))
  simpa only [Matrix.IsHermitian.eigenvalues,complexNoncentralSampleSmallestEigenvalue,e,
    Equiv.symm_apply_apply] using h

def actualNoncentralInverseMinimumTail (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (r : ℝ) : ℝ :=
  (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
    {z | r ≤ (complexNoncentralSampleSmallestEigenvalue M (Nat.succ_pos n) z)⁻¹}

theorem actualNoncentralInverseMinimumTail_eq (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (r : ℝ) (hr : 0 < r) :
    actualNoncentralInverseMinimumTail d n M r = actualNoncentralMinimumCDF d n M r⁻¹ := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [actualNoncentral_minimum_pos_ae (Nat.succ_pos n) (by omega) M] with z hz
  apply propext
  simp only [Set.mem_setOf_eq,inv_eq_one_div,le_div_iff₀ hz,le_div_iff₀ hr,mul_comm]

theorem actualNoncentralInverseMinimumTail_log_exponent (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) :
    Tendsto (fun r : ℝ => Real.log (actualNoncentralInverseMinimumTail d n M r)/Real.log r)
      atTop (𝓝 (-((d+1 : ℕ) : ℝ))) := by
  apply (actualNoncentralMinimumCDF_highSNR_diversity d n M 1 (by norm_num)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [actualNoncentralInverseMinimumTail_eq d n M r hr,one_div]

theorem actualNoncentralInverseMinimumTail_power_bounds (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (r : ℝ) (hr : 4 ≤ r) :
    noncentralMinimumPowerLower d n M/r^(d+1) ≤ actualNoncentralInverseMinimumTail d n M r ∧
    actualNoncentralInverseMinimumTail d n M r ≤ noncentralMinimumPowerUpper d n M/r^(d+1) := by
  have hrp : 0 < r := by linarith
  have hs : r⁻¹ ≤ (1/4 : ℝ) := by
    rw [inv_eq_one_div,div_le_iff₀ hrp]
    linarith
  rw [actualNoncentralInverseMinimumTail_eq d n M r hrp]
  simpa only [inv_pow,div_eq_mul_inv] using
    actualNoncentralMinimumCDF_local_power_bounds d n M r⁻¹ (inv_pos.mpr hrp) hs

end
end JinWishart
#print axioms JinWishart.actualNoncentral_minimum_pos_ae
#print axioms JinWishart.actualNoncentralInverseMinimumTail_eq
#print axioms JinWishart.actualNoncentralInverseMinimumTail_log_exponent
#print axioms JinWishart.actualNoncentralInverseMinimumTail_power_bounds
