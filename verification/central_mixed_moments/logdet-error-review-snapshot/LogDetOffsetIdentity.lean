import JinWishartFormalization.FiniteSpectrumLogDetGrowth

/-! Exact pointwise finite-spectrum offset remainder. Codex deterministic algebra. -/
namespace JinWishart
noncomputable section

theorem log_multiplicative_inverse_error (r x : ℝ) (hr : 0 < r) (hx : 0 < x) :
    Real.log (1+r*x)-Real.log r-Real.log x = Real.log (1+(r*x)⁻¹) := by
  have hrx := mul_pos hr hx
  have hp : 0 < 1+(r*x)⁻¹ := by positivity
  rw [show 1+r*x=(r*x)*(1+(r*x)⁻¹) by field_simp [hrx.ne']; ring,
    Real.log_mul hrx.ne' hp.ne',Real.log_mul hr.ne' hx.ne']
  ring

theorem finiteSpectrumLogDet_offset_error {ι : Type*} [Fintype ι]
    (l : ι → ℝ) (hl : ∀ i, 0 < l i) (r : ℝ) (hr : 0 < r) :
    finiteSpectrumLogDet l r-(Fintype.card ι : ℝ)*Real.log r-∑ i, Real.log (l i) =
      ∑ i, Real.log (1+(r*l i)⁻¹) := by
  classical
  calc
    _ = ∑ i, (Real.log (1+r*l i)-Real.log r-Real.log (l i)) := by
      simp [finiteSpectrumLogDet,Finset.sum_sub_distrib]
    _ = _ := Finset.sum_congr rfl (fun i _ => log_multiplicative_inverse_error r (l i) hr (hl i))

end
end JinWishart
#print axioms JinWishart.log_multiplicative_inverse_error
#print axioms JinWishart.finiteSpectrumLogDet_offset_error
