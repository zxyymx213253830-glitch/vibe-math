import JinWishartFormalization.FiniteSpectrumOffsetInverseRate
import Mathlib.Analysis.MeanInequalitiesPow

/-! Fractional finite-spectrum offset majorant. Codex.
Controls seed2026102241:1323 finite/Gamma subcritical controls, with a
missing-1/alpha negative control. [需人工审查] Stochastic use of real powers. -/
namespace JinWishart
noncomputable section

private theorem logOneAddFractional (x α : ℝ) (hx : 0≤x) (ha : 0<α) (ha1 : α≤1) :
    Real.log (1+x)≤x^α/α := by
  have hp : 0<1+x := by positivity
  have hpow := Real.rpow_add_le_add_rpow (show (0 : ℝ)≤1 by norm_num) hx ha.le ha1
  rw [Real.one_rpow] at hpow
  have hh := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp α)
  rw [Real.log_rpow hp α] at hh
  apply (le_div_iff₀ ha).mpr
  nlinarith

theorem positiveModeOffsetError_fractional_bound (x t α : ℝ)
    (hx : 0≤x) (ht : 0<t) (ha : 0<α) (ha1 : α≤1) :
    0≤positiveModeOffsetError x t ∧
      positiveModeOffsetError x t≤α⁻¹*(t⁻¹)^α*(x⁻¹)^α := by
  refine ⟨(positiveModeOffsetError_nonneg_le_inverse x t hx ht).1,?_⟩
  by_cases hp : 0<x
  · have harg : 0<1+t⁻¹*x⁻¹ := by positivity
    have he : 1+t*x=(t*x)*(1+t⁻¹*x⁻¹) := by field_simp [ht.ne',hp.ne'];ring
    have herr : positiveModeOffsetError x t=Real.log (1+t⁻¹*x⁻¹) := by
      unfold positiveModeOffsetError positiveSpectrumLog
      rw [if_pos hp,one_mul,he,Real.log_mul (mul_ne_zero ht.ne' hp.ne') harg.ne',
        Real.log_mul ht.ne' hp.ne']
      simp only [if_pos hp]
      ring
    rw [herr]
    have hh := logOneAddFractional (t⁻¹*x⁻¹) α (by positivity) ha ha1
    rw [Real.mul_rpow (inv_nonneg.mpr ht.le) (inv_nonneg.mpr hp.le),div_eq_mul_inv] at hh
    convert hh using 1 <;> ring
  · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
    simp [hz,positiveModeOffsetError,positiveSpectrumLog,Real.zero_rpow ha.ne']

theorem finiteSpectrumOffsetError_fractional_min_bound {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i,0≤x i) (a t α : ℝ) (ha : 0<a) (ht : 0<t)
    (hα : 0<α) (hα1 : α≤1) (hmin : ∀ i,0<x i → a≤x i) :
    0≤(∑ i,positiveModeOffsetError (x i) t) ∧
      (∑ i,positiveModeOffsetError (x i) t)≤
        (Fintype.card ι : ℝ)*α⁻¹*(t⁻¹)^α*(a⁻¹)^α := by
  classical
  constructor
  · exact Finset.sum_nonneg (fun i _ => (positiveModeOffsetError_fractional_bound (x i) t α (hx i) ht hα hα1).1)
  · have hb (i : ι) : positiveModeOffsetError (x i) t≤α⁻¹*(t⁻¹)^α*(a⁻¹)^α := by
      by_cases hp : 0<x i
      · apply (positiveModeOffsetError_fractional_bound (x i) t α (hx i) ht hα hα1).2.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤α⁻¹*(t⁻¹)^α)
        apply Real.rpow_le_rpow (inv_nonneg.mpr hp.le) _ hα.le
        simpa only [one_div] using one_div_le_one_div_of_le ha (hmin i hp)
      · have hz : x i=0 := le_antisymm (le_of_not_gt hp) (hx i)
        simp only [hz,positiveModeOffsetError,positiveSpectrumLog,lt_self_iff_false,
          if_false,mul_zero,add_zero,Real.log_one,zero_mul,sub_zero]
        positivity
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hh

end
end JinWishart
#print axioms JinWishart.positiveModeOffsetError_fractional_bound
#print axioms JinWishart.finiteSpectrumOffsetError_fractional_min_bound
