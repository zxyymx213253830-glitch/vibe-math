import JinWishartFormalization.PsiCandidateTailRatio

/-! Codex. Seed 2026103102 independent Psi/lower integral controls precede
source. Candidate largest-coordinate CDF only; no actual Wishart joint-law
identification. [需人工审查] Fubini, event and paper conventions. -/
open MeasureTheory Matrix Set
namespace JinWishart
noncomputable section

theorem mixedCandidateLowerMatrix_det_eq_restricted (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (x : ℝ) (hx : 0 ≤ x) :
 ((mixedCandidateTailMatrix p L q lambda 0) - (mixedCandidateTailMatrix p L q lambda x)).det =
 (Matrix.of (fun i j => ∫ y in Iic x,
   mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det := by
 let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
 let A : Matrix (Fin (p+L)) (Fin (p+L)) ℝ := Matrix.of (fun i j => ∫ y in Iic x,
   mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y ∂μ)
 have h : mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x =
     A.submatrix finSumFinEquiv finSumFinEquiv := by
   ext i j
   have hI := (mixedEnsemble_pair_moment p L q lambda hl (finSumFinEquiv i) (finSumFinEquiv j)).1
   have ht := setIntegral_compl (μ := μ) (s := Ioi x) (f := fun y => mixedEnsembleF p L (finSumFinEquiv i) y *
     mixedEnsembleG p L q lambda (finSumFinEquiv j) y) measurableSet_Ioi hI
   simp only [compl_Ioi] at ht
   simp only [Matrix.sub_apply,mixedCandidateTailMatrix,A,Matrix.of_apply,Matrix.submatrix_apply]
   have hxint : (∫ y in Ioi x, mixedEnsembleF p L (finSumFinEquiv i) y *
     mixedEnsembleG p L q lambda (finSumFinEquiv j) y ∂μ) =
     ∫ y in Ioi x, mixedEnsembleF p L (finSumFinEquiv i) y *
       mixedEnsembleG p L q lambda (finSumFinEquiv j) y := by
     rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hx)]
   rw [hxint] at ht
   exact ht.symm
 rw [h,Matrix.det_submatrix_equiv_self]

theorem paperPsi_lower_det_norm (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (x : ℝ) (hx : 0 ≤ x) :
 ‖((theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0) -
    (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)).det‖ =
 (∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) *
   |((mixedCandidateTailMatrix p L q lambda 0) - (mixedCandidateTailMatrix p L q lambda x)).det| := by
 let B := theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0 -
   theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x
 have h := norm_det_submatrix_equiv_equiv_complex (psiZeroRowEquiv p L) (psiZeroColumnEquiv p L) B
 have hb : B.submatrix (psiZeroRowEquiv p L) (psiZeroColumnEquiv p L) =
   Complex.ofRealHom.mapMatrix (Matrix.of (fun i j => psiTailColumnFactor p L q lambda j *
     (mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x) i j)) := by
   ext i j
   have h0 := congrArg (fun A => A i j) (paperPsi_tail_matrix_transport p L q lambda hl 0 le_rfl)
   have hx' := congrArg (fun A => A i j) (paperPsi_tail_matrix_transport p L q lambda hl x hx)
   change theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0
     (psiZeroRowEquiv p L i) (psiZeroColumnEquiv p L j) =
     ((psiTailColumnFactor p L q lambda j * mixedCandidateTailMatrix p L q lambda 0 i j : ℝ) : ℂ) at h0
   change theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x
     (psiZeroRowEquiv p L i) (psiZeroColumnEquiv p L j) =
     ((psiTailColumnFactor p L q lambda j * mixedCandidateTailMatrix p L q lambda x i j : ℝ) : ℂ) at hx'
   change theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0
     (psiZeroRowEquiv p L i) (psiZeroColumnEquiv p L j) -
     theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x
     (psiZeroRowEquiv p L i) (psiZeroColumnEquiv p L j) =
     ((psiTailColumnFactor p L q lambda j * (mixedCandidateTailMatrix p L q lambda 0 i j -
       mixedCandidateTailMatrix p L q lambda x i j) : ℝ) : ℂ)
   rw [h0,hx']
   push_cast
   ring
 rw [← h,hb,← Complex.ofRealHom.map_det]
 change ‖(((Matrix.of (fun i j => psiTailColumnFactor p L q lambda j *
   (mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x) i j)).det : ℝ) : ℂ)‖ = _
 rw [Complex.norm_real,Real.norm_eq_abs,Matrix.det_mul_row,abs_mul]
 have hp : 0 ≤ ∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j := by
   apply Finset.prod_nonneg
   intro j _
   cases j with
   | inl a => simp [psiTailColumnFactor]
   | inr b => simp only [psiTailColumnFactor]; positivity
 rw [abs_of_nonneg hp]

theorem mixedCandidateLowerMatrix_det_nonneg (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x) :
 0 ≤ (mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x).det := by
 have h := mixedCandidateEnsemble_all_le p L q lambda hl hlp x
 rw [← mixedCandidateLowerMatrix_det_eq_restricted p L q lambda (fun j => (hlp j).le) x hx] at h
 have hd := mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp
 have hr : 0 ≤ (mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x).det /
   (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
     (mixedEnsembleG p L q lambda)).det := by
   rw [← h]
   exact ENNReal.toReal_nonneg
 have hmul := mul_nonneg hr (le_of_lt hd)
 have he : (mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x).det /
   (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
     (mixedEnsembleG p L q lambda)).det *
   (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
     (mixedEnsembleG p L q lambda)).det =
       (mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x).det :=
   div_mul_cancel₀ _ (ne_of_gt hd)
 rwa [he] at hmul

theorem mixedCandidateEnsemble_all_le_eq_paperPsi_ratio
 (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x) :
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, z i ≤ x}).toReal =
 ‖((theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0) -
    (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)).det‖ /
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
 have hn := mixedCandidateLowerMatrix_det_nonneg p L q lambda hl hlp x hx
 have h0 := mixedCandidateTailMatrix_det_nonneg p L q lambda hl hlp 0 le_rfl
 rw [mixedCandidateEnsemble_all_le p L q lambda hl hlp x,
   ← mixedCandidateLowerMatrix_det_eq_restricted p L q lambda (fun j => (hlp j).le) x hx,
   paperPsi_lower_det_norm p L q lambda (fun j => (hlp j).le) x hx,
   paperPsi_tail_det_norm p L q lambda (fun j => (hlp j).le) 0 le_rfl,
   abs_of_nonneg hn,abs_of_nonneg h0,mixedCandidateTailMatrix_zero_det]
 field_simp

end
end JinWishart
#print axioms JinWishart.mixedCandidateLowerMatrix_det_eq_restricted
#print axioms JinWishart.paperPsi_lower_det_norm
#print axioms JinWishart.mixedCandidateLowerMatrix_det_nonneg
#print axioms JinWishart.mixedCandidateEnsemble_all_le_eq_paperPsi_ratio
