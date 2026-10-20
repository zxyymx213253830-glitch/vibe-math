import JinWishartFormalization.NoiselessRowLogDetError
import JinWishartFormalization.HermitianInverseTrace
import JinWishartFormalization.LogOneAddTaylorBounds

/-! Deterministic inverse-trace first correction with a global half-quadratic bound.
Codex. ROW direction and ordinary inverse throughout.
-/
open Matrix
namespace JinWishart
noncomputable section

theorem scaled_log_inverse_first_correction_bounds (r x : ℝ) (hr : 0<r) (hx : 0<x) :
    0≤x⁻¹-r*Real.log (1+(r*x)⁻¹) ∧
    x⁻¹-r*Real.log (1+(r*x)⁻¹)≤1/(2*r*x^2) := by
  have h := log_one_add_quadratic_gap_bounds ((r*x)⁻¹) (by positivity)
  have h0 := mul_nonneg hr.le h.1
  have h2 := mul_le_mul_of_nonneg_left h.2 hr.le
  have he : r*((r*x)⁻¹-Real.log (1+(r*x)⁻¹))=x⁻¹-r*Real.log (1+(r*x)⁻¹) := by
    field_simp [hr.ne',hx.ne'] <;> ring
  rw [he] at h0 h2
  refine ⟨h0,?_⟩
  convert h2 using 1 <;> field_simp [hr.ne',hx.ne'] <;> ring

theorem finiteSpectrum_inverse_first_correction_bounds {ι : Type*} [Fintype ι]
    (l : ι → ℝ) (δ r : ℝ) (hδ : 0<δ) (hl : ∀ i, δ≤l i) (hr : 0<r) :
    0≤(∑ i, (l i)⁻¹)-r*(∑ i, Real.log (1+(r*l i)⁻¹)) ∧
    (∑ i, (l i)⁻¹)-r*(∑ i, Real.log (1+(r*l i)⁻¹))≤
      (Fintype.card ι:ℝ)/(2*r*δ^2) := by
  classical
  have hb (i : ι) : 0≤(l i)⁻¹-r*Real.log (1+(r*l i)⁻¹) ∧
      (l i)⁻¹-r*Real.log (1+(r*l i)⁻¹)≤1/(2*r*δ^2) := by
    have h := scaled_log_inverse_first_correction_bounds r (l i) hr (hδ.trans_le (hl i))
    refine ⟨h.1,h.2.trans ?_⟩
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le (hl i) 2) (by positivity))
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hb i).1)
  · calc
      _ ≤ ∑ _i : ι, 1/(2*r*δ^2) := Finset.sum_le_sum (fun i _ => (hb i).2)
      _ = _ := by simp [div_eq_mul_inv]

theorem rowLogDet_first_correction_bounds {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m) (δ r : ℝ)
    (hδ : 0<δ) (hfloor : δ≤gramSmallestValue Xᴴ hm) (hr : 0<r) :
    0≤((complexGram Xᴴ)⁻¹).trace.re-r*(
      Real.log ((1+(r:ℂ) • complexGram X).det.re)-(m:ℝ)*Real.log r-
        Real.log ((complexGram Xᴴ).det.re)) ∧
    ((complexGram Xᴴ)⁻¹).trace.re-r*(
      Real.log ((1+(r:ℂ) • complexGram X).det.re)-(m:ℝ)*Real.log r-
        Real.log ((complexGram Xᴴ).det.re)) ≤ (m:ℝ)/(2*r*δ^2) := by
  have hf (i : Fin (Fintype.card (Fin m))) :
      δ≤(complexGram_posSemidef Xᴴ).1.eigenvalues₀ i :=
    hfloor.trans (gramSmallestValue_le_orderedEigenvalue Xᴴ hm i)
  have hi := hermitian_trace_inverse_pow_eq_orderedEigenvalues (complexGram Xᴴ)
    (complexGram_posSemidef Xᴴ).1 (fun i => (hδ.trans_le (hf i)).ne') 1
  simp only [pow_one] at hi
  rw [hi,rowLogDet_offset_error_identity X hm δ r hδ hfloor hr]
  simpa only [Fintype.card_fin] using finiteSpectrum_inverse_first_correction_bounds _ δ r hδ hf hr

end
end JinWishart
#print axioms JinWishart.scaled_log_inverse_first_correction_bounds
#print axioms JinWishart.finiteSpectrum_inverse_first_correction_bounds
#print axioms JinWishart.rowLogDet_first_correction_bounds
