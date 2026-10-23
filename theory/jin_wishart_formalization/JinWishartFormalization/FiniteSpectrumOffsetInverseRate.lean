import JinWishartFormalization.FiniteSpectrumOffsetL2

/-! Quantitative finite-spectrum high-scale offset bounds. Codex.
Controls seed2026102239:72 finite spectra plus Gamma3/4 inverse-square
calibration,807 checks. [需人工审查] Subsequent stochastic domination. -/
open MeasureTheory
namespace JinWishart
noncomputable section

theorem positiveModeOffsetError_nonneg_le_inverse (x r : ℝ) (hx : 0≤x) (hr : 0<r) :
    0≤positiveModeOffsetError x r ∧ positiveModeOffsetError x r≤r⁻¹*x⁻¹ := by
  by_cases hp : 0<x
  · have ht : 0<1+r⁻¹*x⁻¹ := by positivity
    have he : 1+r*x=(r*x)*(1+r⁻¹*x⁻¹) := by field_simp [hr.ne',hp.ne'];ring
    have herr : positiveModeOffsetError x r=Real.log (1+r⁻¹*x⁻¹) := by
      unfold positiveModeOffsetError positiveSpectrumLog
      rw [if_pos hp,one_mul,he,Real.log_mul (mul_ne_zero hr.ne' hp.ne') ht.ne',
        Real.log_mul hr.ne' hp.ne']
      simp only [if_pos hp]
      ring
    rw [herr]
    constructor
    · apply Real.log_nonneg
      have hh : 0≤r⁻¹*x⁻¹ := by positivity
      linarith
    · have hh := Real.log_le_sub_one_of_pos ht
      linarith
  · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
    simp [hz,positiveModeOffsetError,positiveSpectrumLog]

theorem finiteSpectrumOffsetError_nonneg_le_min_inverse {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i,0≤x i) (a r : ℝ) (ha : 0<a) (hr : 0<r)
    (hmin : ∀ i,0<x i → a≤x i) :
    0≤(∑ i,positiveModeOffsetError (x i) r) ∧
      (∑ i,positiveModeOffsetError (x i) r)≤(Fintype.card ι : ℝ)*r⁻¹*a⁻¹ := by
  classical
  constructor
  · exact Finset.sum_nonneg (fun i _ => (positiveModeOffsetError_nonneg_le_inverse (x i) r (hx i) hr).1)
  · have hb (i : ι) : positiveModeOffsetError (x i) r≤r⁻¹*a⁻¹ := by
      by_cases hp : 0<x i
      · apply (positiveModeOffsetError_nonneg_le_inverse (x i) r (hx i) hr).2.trans
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
        simpa only [one_div] using one_div_le_one_div_of_le ha (hmin i hp)
      · have hz : x i=0 := le_antisymm (le_of_not_gt hp) (hx i)
        simp only [hz,positiveModeOffsetError,positiveSpectrumLog,lt_self_iff_false,
          if_false,mul_zero,add_zero,Real.log_one,zero_mul,sub_zero]
        positivity
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hh

end
end JinWishart
#print axioms JinWishart.positiveModeOffsetError_nonneg_le_inverse
#print axioms JinWishart.finiteSpectrumOffsetError_nonneg_le_min_inverse
