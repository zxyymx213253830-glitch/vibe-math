import JinWishartFormalization.PaperPsiTailMomentBridge
import JinWishartFormalization.MixedCandidateExtremeEvents

/-! Codex. Seed 2026103010: 54 numerical and 24 negative controls precede
source. Formula-side candidate versus original Psi tail only; no actual
Wishart law is claimed. [需人工审查] Measure restrictions and paper mapping. -/
open MeasureTheory Matrix Set
namespace JinWishart
noncomputable section

theorem norm_det_submatrix_equiv_equiv_complex {a b : Type*} [Fintype a]
 [Fintype b] [DecidableEq a] [DecidableEq b] (er ec : a ≃ b)
 (A : Matrix b b ℂ) : ‖(A.submatrix er ec).det‖ = ‖A.det‖ := by
 have h : (A.submatrix er ec).det =
   ((Equiv.Perm.sign (ec.symm.trans er) : ℤˣ) : ℂ) * A.det := by
   change (A.reindex er.symm ec.symm).det = _
   rw [Matrix.det_reindex]
   simp only [Equiv.symm_symm]
 rw [h,norm_mul]
 have hs : ‖((Equiv.Perm.sign (ec.symm.trans er) : ℤˣ) : ℂ)‖ = 1 := by
   change ‖(((Equiv.Perm.sign (ec.symm.trans er) : ℤˣ) : ℤ) : ℂ)‖ = 1
   rw [Complex.norm_intCast,abs_unit_intCast]
 rw [hs,one_mul]

theorem mixedCandidateTailMatrix_det_eq_restricted (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : ℝ) (hx : 0 ≤ x) :
 (mixedCandidateTailMatrix p L q lambda x).det =
 (Matrix.of (fun i j => ∫ y in Ioi x,
   mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det := by
 let A : Matrix (Fin (p+L)) (Fin (p+L)) ℝ := Matrix.of (fun i j => ∫ y in Ioi x,
   mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))
 have h : mixedCandidateTailMatrix p L q lambda x =
   A.submatrix finSumFinEquiv finSumFinEquiv := by
   ext i j
   simp only [mixedCandidateTailMatrix,A,Matrix.of_apply,Matrix.submatrix_apply]
   rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hx)]
 rw [h,Matrix.det_submatrix_equiv_self]

theorem paperPsi_tail_det_norm (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (x : ℝ) (hx : 0 ≤ x) :
 ‖(theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).det‖ =
 (∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) *
   |(mixedCandidateTailMatrix p L q lambda x).det| := by
 have h := norm_det_submatrix_equiv_equiv_complex (psiZeroRowEquiv p L)
   (psiZeroColumnEquiv p L)
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)
 rw [← h,paperPsi_tail_matrix_transport p L q lambda hl x hx,
   ← Complex.ofRealHom.map_det]
 change ‖(((Matrix.of (fun i j => psiTailColumnFactor p L q lambda j *
   mixedCandidateTailMatrix p L q lambda x i j)).det : ℝ) : ℂ)‖ = _
 rw [Complex.norm_real,Real.norm_eq_abs,Matrix.det_mul_row,abs_mul]
 have hp : 0 ≤ ∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j := by
   apply Finset.prod_nonneg
   intro j _
   cases j with
   | inl a => simp [psiTailColumnFactor]
   | inr b => simp only [psiTailColumnFactor]; positivity
 rw [abs_of_nonneg hp]

theorem mixedCandidateTailMatrix_zero_det (p L q : ℕ) (lambda : Fin L → ℝ) :
 (mixedCandidateTailMatrix p L q lambda 0).det =
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
   (mixedEnsembleG p L q lambda)).det := by
 have h := mixedCandidateTailMatrix_det_eq_restricted p L q lambda 0 le_rfl
 simpa only [Measure.restrict_restrict_of_subset (Subset.rfl),determinantMomentMatrix] using h

theorem mixedCandidateTailMatrix_det_nonneg (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x) :
 0 ≤ (mixedCandidateTailMatrix p L q lambda x).det := by
 have h := mixedCandidateEnsemble_all_gt p L q lambda hl hlp x
 rw [← mixedCandidateTailMatrix_det_eq_restricted p L q lambda x hx] at h
 have hd := mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp
 have hr : 0 ≤ (mixedCandidateTailMatrix p L q lambda x).det /
   (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
     (mixedEnsembleG p L q lambda)).det := by
   rw [← h]
   exact ENNReal.toReal_nonneg
 have hmul := mul_nonneg hr (le_of_lt hd)
 have he : (mixedCandidateTailMatrix p L q lambda x).det /
   (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
     (mixedEnsembleG p L q lambda)).det *
   (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
     (mixedEnsembleG p L q lambda)).det =
       (mixedCandidateTailMatrix p L q lambda x).det := div_mul_cancel₀ _ (ne_of_gt hd)
 rwa [he] at hmul

theorem mixedCandidateEnsemble_all_gt_eq_paperPsi_ratio
 (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x) :
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, x < z i}).toReal =
 ‖(theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).det‖ /
 ‖(theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det‖ := by
 have hp : 0 < ∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j := by
   apply Finset.prod_pos
   intro j _
   cases j with
   | inl a => simp [psiTailColumnFactor]
   | inr b =>
       simp only [psiTailColumnFactor]
       exact mul_pos (pow_pos (Real.sqrt_pos.2 (hlp b)) _) (Real.exp_pos _)
 have hd := mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp
 have hn := mixedCandidateTailMatrix_det_nonneg p L q lambda hl hlp x hx
 have h0 := mixedCandidateTailMatrix_det_nonneg p L q lambda hl hlp 0 le_rfl
 rw [mixedCandidateEnsemble_all_gt p L q lambda hl hlp x,
   ← mixedCandidateTailMatrix_det_eq_restricted p L q lambda x hx,
   paperPsi_tail_det_norm p L q lambda (fun j => (hlp j).le) x hx,
   paperPsi_tail_det_norm p L q lambda (fun j => (hlp j).le) 0 le_rfl,
   abs_of_nonneg hn, abs_of_nonneg h0,
   mixedCandidateTailMatrix_zero_det]
 field_simp

end
end JinWishart
#print axioms JinWishart.norm_det_submatrix_equiv_equiv_complex
#print axioms JinWishart.mixedCandidateTailMatrix_det_eq_restricted
#print axioms JinWishart.paperPsi_tail_det_norm
#print axioms JinWishart.mixedCandidateTailMatrix_zero_det
#print axioms JinWishart.mixedCandidateTailMatrix_det_nonneg
#print axioms JinWishart.mixedCandidateEnsemble_all_gt_eq_paperPsi_ratio
