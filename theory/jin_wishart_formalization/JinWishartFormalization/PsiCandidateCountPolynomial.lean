import JinWishartFormalization.RowAffineDeterminantTransport
import JinWishartFormalization.PsiCandidateLargestCDF
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! Codex. Seeds 2026103104/05 candidate count and exact polynomial transport
controls precede source. Formula-side count polynomial only; no actual Wishart
joint law or journal T3 normalization claim. [需人工审查] Indices and Fubini. -/
open MeasureTheory Matrix Set Polynomial Finset
namespace JinWishart
noncomputable section

def psiCountPolynomial (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ) : Polynomial ℂ :=
 (rowAffinePolynomialMatrix
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)
   (theorem2XiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)).det

def mixedCandidateCountPolynomial (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ) : Polynomial ℝ :=
 (rowAffinePolynomialMatrix (mixedCandidateTailMatrix p L q lambda x)
   (mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x)).det

theorem psiCountPolynomial_transport (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (x : ℝ) (hx : 0 ≤ x) :
 Polynomial.C (((Equiv.Perm.sign ((psiZeroColumnEquiv p L).symm.trans
   (psiZeroRowEquiv p L)) : ℤˣ) : ℂ)) * psiCountPolynomial p L q lambda x =
 Polynomial.C (((∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) : ℝ) : ℂ) *
   (mixedCandidateCountPolynomial p L q lambda x).map Complex.ofRealHom := by
 let er := psiZeroRowEquiv p L
 let ec := psiZeroColumnEquiv p L
 let A := theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x
 let B := theorem2XiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x
 let T := mixedCandidateTailMatrix p L q lambda x
 let S := mixedCandidateTailMatrix p L q lambda 0 - T
 let d : Fin p ⊕ Fin L → ℝ := psiTailColumnFactor p L q lambda
 have hA : A.submatrix er ec =
     Matrix.of (fun i j => (d j : ℂ) * (T i j : ℂ)) := by
   have h := paperPsi_tail_matrix_transport p L q lambda hl x hx
   ext i j
   have hh := congrArg (fun C => C i j) h
   change _ = ((d j * T i j : ℝ) : ℂ) at hh
   simpa only [A,er,ec,d,T,Matrix.of_apply,Complex.ofReal_mul] using hh
 have hB : B.submatrix er ec =
     Matrix.of (fun i j => (d j : ℂ) * (S i j : ℂ)) := by
   have h0 := paperPsi_tail_matrix_transport p L q lambda hl 0 le_rfl
   have hx' := paperPsi_tail_matrix_transport p L q lambda hl x hx
   have hxi := eq_sub_of_add_eq (theorem2XiMatrix_add_theorem1PsiMatrix
     (p+L) (p+L+q) L (by omega) (by omega) lambda x)
   ext i j
   have hz := congrArg (fun C => C i j) h0
   have ht := congrArg (fun C => C i j) hx'
   change theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0
     (psiZeroRowEquiv p L i) (psiZeroColumnEquiv p L j) =
     ((d j * mixedCandidateTailMatrix p L q lambda 0 i j : ℝ) : ℂ) at hz
   change theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x
     (psiZeroRowEquiv p L i) (psiZeroColumnEquiv p L j) = ((d j * T i j : ℝ) : ℂ) at ht
   change (B.submatrix er ec) i j = _
   simp only [Matrix.submatrix_apply,B,hxi,Matrix.sub_apply,Matrix.of_apply,S,T,d]
   rw [hz,ht]
   push_cast
   ring
 have hr := rowAffine_det_submatrix_complex er ec A B
 have hr' : Polynomial.C (((Equiv.Perm.sign (ec.symm.trans er) : ℤˣ) : ℂ)) *
      (rowAffinePolynomialMatrix A B).det =
      (rowAffinePolynomialMatrix (A.submatrix er ec) (B.submatrix er ec)).det := by
   simpa using hr.symm
 rw [hA,hB] at hr'
 have hc : (rowAffinePolynomialMatrix (Matrix.of (fun i j => (d j : ℂ) * (T i j : ℂ)))
       (Matrix.of (fun i j => (d j : ℂ) * (S i j : ℂ)))).det =
     Polynomial.C (∏ j, (d j : ℂ)) *
       (rowAffinePolynomialMatrix (Complex.ofRealHom.mapMatrix T) (Complex.ofRealHom.mapMatrix S)).det := by
   change (rowAffinePolynomialMatrix
     (Matrix.of (fun i j => (d j : ℂ) * (Complex.ofRealHom.mapMatrix T) i j))
     (Matrix.of (fun i j => (d j : ℂ) * (Complex.ofRealHom.mapMatrix S) i j))).det = _
   exact rowAffine_det_columnScale_complex (fun j => (d j : ℂ))
     (Complex.ofRealHom.mapMatrix T) (Complex.ofRealHom.mapMatrix S)
 rw [hc] at hr'
 have hp : (∏ j : Fin p ⊕ Fin L, (d j : ℂ)) = ((∏ j, d j : ℝ) : ℂ) := by
   push_cast
   rfl
 rw [hp,rowAffine_det_realToComplex] at hr'
 exact hr'

theorem mixedCandidateCountPolynomial_restricted (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (x : ℝ) (hx : 0 ≤ x) :
 mixedCandidateCountPolynomial p L q lambda x =
 (rowAffinePolynomialMatrix
   (Matrix.of (fun i j => ∫ y in Ioi x, mixedEnsembleF p L i y *
     mixedEnsembleG p L q lambda j y ∂(volume.restrict (Ioi (0 : ℝ)))))
   (Matrix.of (fun i j => ∫ y in Iic x, mixedEnsembleF p L i y *
     mixedEnsembleG p L q lambda j y ∂(volume.restrict (Ioi (0 : ℝ)))))).det := by
 let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
 let U : Matrix (Fin (p+L)) (Fin (p+L)) ℝ := Matrix.of (fun i j => ∫ y in Ioi x,
   mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y ∂μ)
 let V : Matrix (Fin (p+L)) (Fin (p+L)) ℝ := Matrix.of (fun i j => ∫ y in Iic x,
   mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y ∂μ)
 have hu : mixedCandidateTailMatrix p L q lambda x = U.submatrix finSumFinEquiv finSumFinEquiv := by
   ext i j
   simp only [mixedCandidateTailMatrix,U,Matrix.of_apply,Matrix.submatrix_apply]
   rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hx)]
 have hv : mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x =
   V.submatrix finSumFinEquiv finSumFinEquiv := by
   ext i j
   have hI := (mixedEnsemble_pair_moment p L q lambda hl (finSumFinEquiv i) (finSumFinEquiv j)).1
   have ht := setIntegral_compl (μ := μ) (s := Ioi x) (f := fun y => mixedEnsembleF p L (finSumFinEquiv i) y *
     mixedEnsembleG p L q lambda (finSumFinEquiv j) y) measurableSet_Ioi hI
   simp only [compl_Ioi] at ht
   simp only [Matrix.sub_apply,mixedCandidateTailMatrix,V,Matrix.of_apply,Matrix.submatrix_apply]
   have hxint : (∫ y in Ioi x, mixedEnsembleF p L (finSumFinEquiv i) y *
     mixedEnsembleG p L q lambda (finSumFinEquiv j) y ∂μ) =
     ∫ y in Ioi x, mixedEnsembleF p L (finSumFinEquiv i) y *
       mixedEnsembleG p L q lambda (finSumFinEquiv j) y := by
     rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hx)]
   rw [hxint] at ht
   exact ht.symm
 unfold mixedCandidateCountPolynomial
 rw [hv,hu]
 change ((rowAffinePolynomialMatrix U V).submatrix finSumFinEquiv finSumFinEquiv).det = _
 exact Matrix.det_submatrix_equiv_self _ _

theorem mixedCandidateEnsemble_count_tail_polynomial (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x)
 (k : ℕ) (hk : k ≤ p+L) :
 ((mixedCandidateEnsemble p L q lambda)
   {z | coordinateMembershipCount (Ioi x) z = k}).toReal =
 (mixedCandidateCountPolynomial p L q lambda x).coeff k /
   (mixedCandidateTailMatrix p L q lambda 0).det := by
 rw [mixedCandidateCountPolynomial_restricted p L q lambda (fun j => (hlp j).le) x hx,
   mixedCandidateTailMatrix_zero_det]
 simpa only [compl_Ioi] using mixedCandidateEnsemble_count p L q lambda hl hlp
   (Ioi x) measurableSet_Ioi k hk

theorem paperPsi_zero_det_signed_transport (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) :
 (((Equiv.Perm.sign ((psiZeroColumnEquiv p L).symm.trans
   (psiZeroRowEquiv p L)) : ℤˣ) : ℂ)) *
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det =
 (((∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) : ℝ) : ℂ) *
   ((mixedCandidateTailMatrix p L q lambda 0).det : ℂ) := by
 let A := theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0
 have h : (A.submatrix (psiZeroRowEquiv p L) (psiZeroColumnEquiv p L)).det =
   (((Equiv.Perm.sign ((psiZeroColumnEquiv p L).symm.trans
     (psiZeroRowEquiv p L)) : ℤˣ) : ℂ)) * A.det := by
   change (A.reindex (psiZeroRowEquiv p L).symm (psiZeroColumnEquiv p L).symm).det = _
   rw [Matrix.det_reindex]
   simp only [Equiv.symm_symm]
 rw [← h,paperPsi_tail_matrix_transport p L q lambda hl 0 le_rfl,
   ← Complex.ofRealHom.map_det,Matrix.det_mul_row]
 change (((∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) *
   (mixedCandidateTailMatrix p L q lambda 0).det : ℝ) : ℂ) = _
 push_cast
 rfl

theorem mixedCandidateEnsemble_count_eq_psi_coefficient (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x)
 (k : ℕ) (hk : k ≤ p+L) :
 (((mixedCandidateEnsemble p L q lambda)
   {z | coordinateMembershipCount (Ioi x) z = k}).toReal : ℂ) =
 (psiCountPolynomial p L q lambda x).coeff k /
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det := by
 let s : ℂ := (((Equiv.Perm.sign ((psiZeroColumnEquiv p L).symm.trans
   (psiZeroRowEquiv p L)) : ℤˣ) : ℂ))
 let f : ℂ := (((∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) : ℝ) : ℂ)
 let d : ℝ := (mixedCandidateTailMatrix p L q lambda 0).det
 let z : ℂ := (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det
 have hp := psiCountPolynomial_transport p L q lambda (fun j => (hlp j).le) x hx
 have hc := congrArg (fun P : Polynomial ℂ => P.coeff k) hp
 simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map] at hc
 change s * (psiCountPolynomial p L q lambda x).coeff k =
   f * ((mixedCandidateCountPolynomial p L q lambda x).coeff k : ℂ) at hc
 have hz := paperPsi_zero_det_signed_transport p L q lambda (fun j => (hlp j).le)
 change s * z = f * (d : ℂ) at hz
 have hs : s ≠ 0 := by
   have hn : ‖s‖ = 1 := by
     change ‖(((Equiv.Perm.sign ((psiZeroColumnEquiv p L).symm.trans
       (psiZeroRowEquiv p L)) : ℤˣ) : ℤ) : ℂ)‖ = 1
     rw [Complex.norm_intCast,abs_unit_intCast]
   intro h
   rw [h,norm_zero] at hn
   norm_num at hn
 have hd : d ≠ 0 := by
   dsimp [d]
   rw [mixedCandidateTailMatrix_zero_det]
   exact ne_of_gt (mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp)
 have hf : f ≠ 0 := by
   dsimp [f]
   have : 0 < ∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j := by
     apply Finset.prod_pos
     intro j _
     cases j with
     | inl a => simp [psiTailColumnFactor]
     | inr b =>
       simp only [psiTailColumnFactor]
       exact mul_pos (pow_pos (Real.sqrt_pos.2 (hlp b)) _) (Real.exp_pos _)
   exact_mod_cast ne_of_gt this
 have hzn : z ≠ 0 := by
   intro h
   rw [h, mul_zero] at hz
   exact (mul_ne_zero hf (by exact_mod_cast hd)) hz.symm
 rw [mixedCandidateEnsemble_count_tail_polynomial p L q lambda hl hlp x hx k hk]
 change (((mixedCandidateCountPolynomial p L q lambda x).coeff k / d : ℝ) : ℂ) = _ / z
 push_cast
 apply (div_eq_div_iff (by exact_mod_cast hd) hzn).2
 apply (mul_left_cancel₀ hs)
 calc
   s * (((mixedCandidateCountPolynomial p L q lambda x).coeff k : ℂ) * z) =
      ((mixedCandidateCountPolynomial p L q lambda x).coeff k : ℂ) * (s * z) := by ring
   _ = ((mixedCandidateCountPolynomial p L q lambda x).coeff k : ℂ) * (f * (d : ℂ)) := by rw [hz]
   _ = (s * (psiCountPolynomial p L q lambda x).coeff k) * (d : ℂ) := by rw [hc]; ring
   _ = s * ((psiCountPolynomial p L q lambda x).coeff k * (d : ℂ)) := by ring

end
end JinWishart
#print axioms JinWishart.psiCountPolynomial_transport
#print axioms JinWishart.mixedCandidateCountPolynomial_restricted
#print axioms JinWishart.mixedCandidateEnsemble_count_tail_polynomial
#print axioms JinWishart.paperPsi_zero_det_signed_transport
#print axioms JinWishart.mixedCandidateEnsemble_count_eq_psi_coefficient
