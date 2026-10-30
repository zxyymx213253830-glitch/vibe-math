import JinWishartFormalization.PsiCandidateCountPolynomial
import JinWishartFormalization.T3PaperThetaSpecialization

/-! Codex. Seed 2026103106 active column permutations with 51 exact symbolic
checks and 21 sign negative controls precede source. Formula-side only.
[需人工审查] Paper index convention and model mapping. -/
open MeasureTheory Matrix Set Polynomial Finset
namespace JinWishart
noncomputable section

def psiActiveColumnPermutation (p L : ℕ) (π : Equiv.Perm (Fin L)) : Equiv.Perm (Fin (p+L)) :=
 (psiZeroColumnEquiv p L).symm.trans
   ((Equiv.sumCongr (Equiv.refl (Fin p)) π).trans (psiZeroColumnEquiv p L))

theorem psiActiveColumnPermutation_inl (p L : ℕ) (π : Equiv.Perm (Fin L)) (a : Fin p) :
 psiActiveColumnPermutation p L π (psiZeroColumnEquiv p L (Sum.inl a)) =
 psiZeroColumnEquiv p L (Sum.inl a) := by
 simp [psiActiveColumnPermutation]

theorem psiActiveColumnPermutation_inr (p L : ℕ) (π : Equiv.Perm (Fin L)) (a : Fin L) :
 psiActiveColumnPermutation p L π (psiZeroColumnEquiv p L (Sum.inr a)) =
 psiZeroColumnEquiv p L (Sum.inr (π a)) := by
 simp [psiActiveColumnPermutation]

theorem psiMatrix_permute_active_columns (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) (x : ℝ) :
 theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) (lambda ∘ π) x =
 (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).submatrix id
   (psiActiveColumnPermutation p L π) := by
 ext i j
 obtain ⟨v, rfl⟩ := (psiZeroColumnEquiv p L).surjective j
 cases v with
 | inl a =>
   simp only [Matrix.submatrix_apply,id_eq]
   rw [psiActiveColumnPermutation_inl]
   have hj : ¬ (psiZeroColumnEquiv p L (Sum.inl a)).val < L := by
     have hc : (psiZeroColumnEquiv p L (Sum.inl a)).val = p+L-(a.val+1) := by
       simp [psiZeroColumnEquiv, Fin.revPerm_apply, Fin.val_rev]; omega
     rw [hc]; omega
   simp [theorem1PsiMatrix,theorem1PsiEntry,Matrix.submatrix_apply,hj]
 | inr a =>
   simp only [Matrix.submatrix_apply,id_eq]
   rw [psiActiveColumnPermutation_inr]
   have hj : (psiZeroColumnEquiv p L (Sum.inr a)).val < L := by change a.val < L; exact a.isLt
   have hj' : (psiZeroColumnEquiv p L (Sum.inr (π a))).val < L := by change (π a).val < L; exact (π a).isLt
   simp only [theorem1PsiMatrix,theorem1PsiEntry,Matrix.submatrix_apply,id_eq, dif_pos hj, dif_pos hj']
   congr 3

theorem xiMatrix_permute_active_columns (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) (x : ℝ) :
 theorem2XiMatrix (p+L) (p+L+q) L (by omega) (by omega) (lambda ∘ π) x =
 (theorem2XiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).submatrix id
   (psiActiveColumnPermutation p L π) := by
 have h1 := theorem2XiMatrix_add_theorem1PsiMatrix (p+L) (p+L+q) L
   (by omega) (by omega) (lambda ∘ π) x
 have h2 := theorem2XiMatrix_add_theorem1PsiMatrix (p+L) (p+L+q) L
   (by omega) (by omega) lambda x
 rw [eq_sub_of_add_eq h1,eq_sub_of_add_eq h2,
   psiMatrix_permute_active_columns p L q lambda π 0,
   psiMatrix_permute_active_columns p L q lambda π x]
 rfl

theorem psiCountPolynomial_permute_active (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) (x : ℝ) :
 psiCountPolynomial p L q (lambda ∘ π) x =
 Polynomial.C (((Equiv.Perm.sign (psiActiveColumnPermutation p L π).symm : ℤˣ) : ℂ)) *
   psiCountPolynomial p L q lambda x := by
 unfold psiCountPolynomial
 rw [psiMatrix_permute_active_columns,xiMatrix_permute_active_columns]
 simpa using rowAffine_det_submatrix_complex (Equiv.refl (Fin (p+L)))
   (psiActiveColumnPermutation p L π)
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)
   (theorem2XiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)

theorem psiZeroDet_permute_active (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) :
 (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) (lambda ∘ π) 0).det =
 (((Equiv.Perm.sign (psiActiveColumnPermutation p L π).symm : ℤˣ) : ℂ)) *
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det := by
 rw [psiMatrix_permute_active_columns]
 change ((theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).reindex
   (Equiv.refl _) (psiActiveColumnPermutation p L π).symm).det = _
 rw [Matrix.det_reindex]
 simp

theorem psiCountRatio_permute_active (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) (x : ℝ) (k : ℕ) :
 (psiCountPolynomial p L q (lambda ∘ π) x).coeff k /
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) (lambda ∘ π) 0).det =
 (psiCountPolynomial p L q lambda x).coeff k /
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det := by
 rw [psiCountPolynomial_permute_active,psiZeroDet_permute_active]
 simp only [Polynomial.coeff_C_mul]
 have hs : (((Equiv.Perm.sign (psiActiveColumnPermutation p L π).symm : ℤˣ) : ℂ)) ≠ 0 := by
   have hn : ‖(((Equiv.Perm.sign (psiActiveColumnPermutation p L π).symm : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
     rw [Complex.norm_intCast,abs_unit_intCast]
   intro h
   rw [h,norm_zero] at hn
   norm_num at hn
 exact mul_div_mul_left _ _ hs

theorem candidateCount_eq_paperThetaDetSum (p L q : ℕ)
 (spectrum : OrderedPositiveNoncentralSpectrum L) (x : ℝ) (hx : 0 ≤ x)
 (k : ℕ) (hk : k ≤ p+L) :
 (((mixedCandidateEnsemble p L q (spectrum.values ∘ Fin.revPerm))
   {z | coordinateMembershipCount (Ioi x) z = k}).toReal : ℂ) =
 theorem3ThetaDetSum (p+L) (p+L+q) L (k+1) (by omega) (by omega) spectrum x /
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) spectrum.values 0).det := by
 have hm : StrictMono (spectrum.values ∘ Fin.revPerm) := by
   intro i j hij
   apply spectrum.strictAnti
   exact Fin.rev_strictAnti hij
 have hp : ∀ j, 0 < (spectrum.values ∘ Fin.revPerm) j := fun j => spectrum.positive _
 rw [mixedCandidateEnsemble_count_eq_psi_coefficient p L q _ hm hp x hx k hk,
   psiCountRatio_permute_active p L q spectrum.values Fin.revPerm x k,
   theorem3ThetaDetSum_eq_polynomialCoefficient]
 simp [psiCountPolynomial]

end
end JinWishart
#print axioms JinWishart.psiActiveColumnPermutation_inl
#print axioms JinWishart.psiActiveColumnPermutation_inr
#print axioms JinWishart.psiMatrix_permute_active_columns
#print axioms JinWishart.xiMatrix_permute_active_columns
#print axioms JinWishart.psiCountPolynomial_permute_active
#print axioms JinWishart.psiZeroDet_permute_active
#print axioms JinWishart.psiCountRatio_permute_active
#print axioms JinWishart.candidateCount_eq_paperThetaDetSum

