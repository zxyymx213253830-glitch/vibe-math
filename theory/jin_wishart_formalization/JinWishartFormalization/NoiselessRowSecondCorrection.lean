import JinWishartFormalization.NoiselessRowFirstCorrection

/-! Deterministic second inverse-trace correction and a positive cubic remainder.
Codex. Global positive-side inequalities; no local power series or probability hypothesis.
-/
open Matrix
namespace JinWishart
noncomputable section

theorem scaled_log_inverse_second_correction_bounds (r x : ℝ) (hr : 0<r) (hx : 0<x) :
    0≤r^2*Real.log (1+(r*x)⁻¹)-r*x⁻¹+(x⁻¹)^2/2 ∧
    r^2*Real.log (1+(r*x)⁻¹)-r*x⁻¹+(x⁻¹)^2/2≤1/(3*r*x^3) := by
  have h := log_one_add_cubic_remainder_bounds ((r*x)⁻¹) (by positivity)
  have h0 := mul_nonneg (sq_nonneg r) h.1
  have h2 := mul_le_mul_of_nonneg_left h.2 (sq_nonneg r)
  have he : r^2*(Real.log (1+(r*x)⁻¹)-(r*x)⁻¹+((r*x)⁻¹)^2/2)=
      r^2*Real.log (1+(r*x)⁻¹)-r*x⁻¹+(x⁻¹)^2/2 := by
    field_simp [hr.ne',hx.ne']
  rw [he] at h0 h2
  refine ⟨h0,?_⟩
  convert h2 using 1 <;> field_simp [hr.ne',hx.ne']

theorem finiteSpectrum_inverse_second_correction_bounds {ι : Type*} [Fintype ι]
    (l : ι → ℝ) (δ r : ℝ) (hδ : 0<δ) (hl : ∀ i, δ≤l i) (hr : 0<r) :
    0≤r^2*(∑ i, Real.log (1+(r*l i)⁻¹))-r*(∑ i, (l i)⁻¹)+(∑ i, ((l i)⁻¹)^2)/2 ∧
    r^2*(∑ i, Real.log (1+(r*l i)⁻¹))-r*(∑ i, (l i)⁻¹)+(∑ i, ((l i)⁻¹)^2)/2≤
      (Fintype.card ι:ℝ)/(3*r*δ^3) := by
  classical
  have hb (i : ι) : 0≤r^2*Real.log (1+(r*l i)⁻¹)-r*(l i)⁻¹+((l i)⁻¹)^2/2 ∧
      r^2*Real.log (1+(r*l i)⁻¹)-r*(l i)⁻¹+((l i)⁻¹)^2/2≤1/(3*r*δ^3) := by
    have h := scaled_log_inverse_second_correction_bounds r (l i) hr (hδ.trans_le (hl i))
    refine ⟨h.1,h.2.trans ?_⟩
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le (hl i) 3) (by positivity))
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_div,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hb i).1)
  · calc
      _ ≤ ∑ _i : ι, 1/(3*r*δ^3) := Finset.sum_le_sum (fun i _ => (hb i).2)
      _ = _ := by simp [div_eq_mul_inv]

theorem rowLogDet_second_correction_bounds {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m) (δ r : ℝ)
    (hδ : 0<δ) (hfloor : δ≤gramSmallestValue Xᴴ hm) (hr : 0<r) :
    0≤r^2*(Real.log ((1+(r:ℂ) • complexGram X).det.re)-(m:ℝ)*Real.log r-
      Real.log ((complexGram Xᴴ).det.re))-r*((complexGram Xᴴ)⁻¹).trace.re+
        (((complexGram Xᴴ)⁻¹)^2).trace.re/2 ∧
    r^2*(Real.log ((1+(r:ℂ) • complexGram X).det.re)-(m:ℝ)*Real.log r-
      Real.log ((complexGram Xᴴ).det.re))-r*((complexGram Xᴴ)⁻¹).trace.re+
        (((complexGram Xᴴ)⁻¹)^2).trace.re/2 ≤ (m:ℝ)/(3*r*δ^3) := by
  have hf (i : Fin (Fintype.card (Fin m))) : δ≤(complexGram_posSemidef Xᴴ).1.eigenvalues₀ i :=
    hfloor.trans (gramSmallestValue_le_orderedEigenvalue Xᴴ hm i)
  have hi := hermitian_trace_inverse_pow_eq_orderedEigenvalues (complexGram Xᴴ)
    (complexGram_posSemidef Xᴴ).1 (fun i => (hδ.trans_le (hf i)).ne') 1
  have h2 := hermitian_trace_inverse_pow_eq_orderedEigenvalues (complexGram Xᴴ)
    (complexGram_posSemidef Xᴴ).1 (fun i => (hδ.trans_le (hf i)).ne') 2
  simp only [pow_one] at hi
  rw [hi,h2,rowLogDet_offset_error_identity X hm δ r hδ hfloor hr]
  simpa only [Fintype.card_fin] using finiteSpectrum_inverse_second_correction_bounds _ δ r hδ hf hr

end
end JinWishart
#print axioms JinWishart.scaled_log_inverse_second_correction_bounds
#print axioms JinWishart.finiteSpectrum_inverse_second_correction_bounds
#print axioms JinWishart.rowLogDet_second_correction_bounds
