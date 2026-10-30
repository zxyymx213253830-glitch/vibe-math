import JinWishartFormalization.MixedLaplaceExponent

/-! Codex. Seed 2026103011 trace Laplace and seed 2026103012 exponent
controls precede source. Candidate trace law only; actual Wishart joint law
is not identified. [需人工审查] Fubini, normalization and model mapping. -/
open MeasureTheory Matrix Finset Set
namespace JinWishart
noncomputable section

theorem weightedMixedColumnFactor_prod (p L : ℕ) (lambda : Fin L → ℝ) (c : ℝ) :
 (∏ j : Fin p ⊕ Fin L, weightedMixedColumnFactor p L lambda c j) =
 (∏ a : Fin p, (c^a.val)⁻¹) * (∏ j : Fin L, Real.exp (lambda j/c)) := by
 rw [Fintype.prod_sum_type]
 rfl

theorem mixedEnsemble_momentMatrix_det (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) :
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det =
 (∏ j : Fin L, Real.exp (lambda j)) * (mixedNoncentralMomentMatrix q p L lambda).det := by
 rw [mixedEnsemble_momentMatrix_eq p L q lambda hl,Matrix.det_submatrix_equiv_self,
   Matrix.det_mul_row,Fintype.prod_sum_type]
 simp [mixedEnsembleColumnFactor]

theorem mixedCandidateEnsemble_trace_laplace_closed (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (s : ℝ) (hs : 0 ≤ s) :
 (∫ z : Fin (p+L) → ℝ, Real.exp (-s * ∑ i, z i) ∂(mixedCandidateEnsemble p L q lambda)) =
 ((1+s)^((p+L)*(p+L+q)))⁻¹ * Real.exp (-s*(∑ j : Fin L, lambda j)/(1+s)) := by
 let c : ℝ := 1+s
 have hc : 0 < c := by dsimp [c]; linarith
 have hcp : c ≠ 0 := ne_of_gt hc
 have hd := mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp
 have hden := mixedEnsemble_momentMatrix_det p L q lambda (fun j => (hlp j).le)
 have hD : (mixedNoncentralMomentMatrix q p L lambda).det ≠ 0 := by
   intro hz
   rw [hden,hz,mul_zero] at hd
   exact (lt_irrefl (0 : ℝ)) hd
 have he : (∏ j : Fin L, Real.exp (lambda j)) ≠ 0 := by positivity
 have hfactors :
   (∏ i : Fin (p+L), (c^(q+i.val+1))⁻¹) *
   (∏ j : Fin p ⊕ Fin L, weightedMixedColumnFactor p L lambda c j) *
   (mixedNoncentralMomentMatrix q p L (fun b => lambda b/c)).det =
   (c^((p+L)*(p+L+q)))⁻¹ * (∏ j : Fin L, Real.exp (lambda j/c)) *
   (mixedNoncentralMomentMatrix q p L lambda).det := by
   rw [weightedMixedColumnFactor_prod,mixedNoncentralMomentMatrix_det_div_scale]
   calc
     _ = ((∏ i : Fin (p+L), (c^(q+i.val+1))⁻¹) *
         (∏ a : Fin p, (c^a.val)⁻¹) *
         (∏ j : Fin L, (c^(p+j.val))⁻¹)) *
         (∏ j : Fin L, Real.exp (lambda j/c)) *
         (mixedNoncentralMomentMatrix q p L lambda).det := by ring
     _ = _ := by rw [mixedLaplace_power_product]
 have hex : (∏ j : Fin L, Real.exp (lambda j/c)) /
     (∏ j : Fin L, Real.exp (lambda j)) =
     Real.exp (-s*(∑ j : Fin L, lambda j)/c) := by
   rw [← Real.exp_sum,← Real.exp_sum,← Real.exp_sub,← Finset.sum_div]
   congr 1
   dsimp [c] at *
   field_simp
   <;> ring
 have h := mixedCandidateEnsemble_trace_laplace_scaled_det p L q lambda hl hlp s hs
 change _ = ((∏ i : Fin (p+L), (c^(q+i.val+1))⁻¹) *
   (∏ j : Fin p ⊕ Fin L, weightedMixedColumnFactor p L lambda c j) *
   (mixedNoncentralMomentMatrix q p L (fun b => lambda b/c)).det) / _ at h
 rw [hfactors,hden] at h
 calc
   _ = ((c^((p+L)*(p+L+q)))⁻¹ * (∏ j : Fin L, Real.exp (lambda j/c)) *
     (mixedNoncentralMomentMatrix q p L lambda).det) /
     ((∏ j : Fin L, Real.exp (lambda j)) * (mixedNoncentralMomentMatrix q p L lambda).det) := h
   _ = (c^((p+L)*(p+L+q)))⁻¹ *
     ((∏ j : Fin L, Real.exp (lambda j/c)) / (∏ j : Fin L, Real.exp (lambda j))) := by field_simp
   _ = _ := by rw [hex]

end
end JinWishart
#print axioms JinWishart.weightedMixedColumnFactor_prod
#print axioms JinWishart.mixedEnsemble_momentMatrix_det
#print axioms JinWishart.mixedCandidateEnsemble_trace_laplace_closed
