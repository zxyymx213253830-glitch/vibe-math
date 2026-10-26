import JinWishartFormalization.OriginalPsiNormalizerNonzero

/-! Codex. Seed2026102611 exact controls precede source.
Explicit norm product for the ORIGINAL Psi(0), allowing nonnegative repeated/zero
formal parameters. No positivity of a candidate ensemble or actual-law assertion.
[需人工审查] Source indexing, formal zero parameters versus physical rank, and later model mapping. -/
open Matrix Finset
namespace JinWishart
noncomputable section

def psiZeroRealMatrix (s t L : ℕ) (lambda : Fin L → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
 Matrix.of (fun i j => if hj : j.val < L then
   Real.rpow (lambda ⟨j.val,hj⟩) (((t-s : ℕ) : ℝ)/2)*
     poissonFactorialMomentPolynomial (t-s) (s-(i.val+1)) (lambda ⟨j.val,hj⟩)
 else (Nat.factorial (theorem1GammaIndex s t i j) : ℝ))

def psiZeroRowEquiv (p L : ℕ) : (Fin p ⊕ Fin L) ≃ Fin (p+L) :=
 finSumFinEquiv.trans Fin.revPerm

def psiZeroColumnEquiv (p L : ℕ) : (Fin p ⊕ Fin L) ≃ Fin (p+L) :=
 (Equiv.sumComm (Fin p) (Fin L)).trans
   ((Equiv.sumCongr (Equiv.refl (Fin L)) (Fin.revPerm : Equiv.Perm (Fin p))).trans
     ((finSumFinEquiv (m := L) (n := p)).trans (finCongr (Nat.add_comm L p))))

def psiZeroColumnScale (p L t : ℕ) (lambda : Fin L → ℝ) : Fin p ⊕ Fin L → ℝ :=
 fun j => match j with
 | Sum.inl _ => 1
 | Sum.inr j => Real.rpow (lambda j) (((t-(p+L) : ℕ) : ℝ)/2)

private theorem realPsiZero_ofReal (s t L : ℕ) (lambda : Fin L → ℝ) :
 theorem1ZeroMomentMatrix s t L lambda = Complex.ofRealHom.mapMatrix (psiZeroRealMatrix s t L lambda) := by
 ext i j
 by_cases hj : j.val < L <;>
   simp [theorem1ZeroMomentMatrix,psiZeroRealMatrix,hj,Complex.ofReal_mul]

theorem psiZeroRealMatrix_transport (p L t : ℕ) (hst : p+L ≤ t) (lambda : Fin L → ℝ) :
 (psiZeroRealMatrix (p+L) t L lambda).submatrix (psiZeroRowEquiv p L) (psiZeroColumnEquiv p L) =
   Matrix.of (fun i j => psiZeroColumnScale p L t lambda j *
     mixedNoncentralMomentMatrix (t-(p+L)) p L lambda i j) := by
 have hr (i : Fin p ⊕ Fin L) :
   p+L-((psiZeroRowEquiv p L i).val+1) = mixedMomentDegree p L i := by
   change p+L-((Fin.rev (finSumFinEquiv i)).val+1) = _
   rw [Fin.val_rev]
   have hi := (finSumFinEquiv (m := p) (n := L) i).isLt
   unfold mixedMomentDegree
   omega
 have hcl (h : Fin p) : (psiZeroColumnEquiv p L (Sum.inl h)).val = p+L-(h.val+1) := by
   change L+(Fin.rev h).val = _
   rw [Fin.val_rev]
   omega
 have hcr (j : Fin L) : (psiZeroColumnEquiv p L (Sum.inr j)).val = j.val := by rfl
 ext i j
 cases j with
 | inl h =>
   have hnot : ¬ (psiZeroColumnEquiv p L (Sum.inl h)).val < L := by rw [hcl]; omega
   have hg : theorem1GammaIndex (p+L) t (psiZeroRowEquiv p L i)
       (psiZeroColumnEquiv p L (Sum.inl h)) = t-(p+L)+mixedMomentDegree p L i+h.val := by
     unfold theorem1GammaIndex
     have hi := (psiZeroRowEquiv p L i).isLt
     have hri := hr i
     rw [hcl]
     omega
   simp [psiZeroRealMatrix,hnot,hg,psiZeroColumnScale,mixedNoncentralMomentMatrix]
 | inr j =>
   have hj : (psiZeroColumnEquiv p L (Sum.inr j)).val < L := by rw [hcr]; exact j.isLt
   have he : (⟨(psiZeroColumnEquiv p L (Sum.inr j)).val,hj⟩ : Fin L) = j := Fin.ext (hcr j)
   simp [psiZeroRealMatrix,hj,he,hr,psiZeroColumnScale,mixedNoncentralMomentMatrix]

private theorem psi_norm_product_decomposed (p L t : ℕ) (hst : p+L ≤ t)
 (lambda : Fin L → ℝ) (hnn : ∀ j, 0 ≤ lambda j) :
 ‖(theorem1PsiMatrix (p+L) t L hst (by omega) lambda 0).det‖ =
   (∏ j : Fin L, Real.rpow (lambda j) (((t-(p+L) : ℕ) : ℝ)/2))*
     ((∏ j : Fin L, lambda j^p)*(∏ i : Fin L, ∏ j ∈ Ioi i, |lambda j-lambda i|))*
       (∏ h : Fin p, (h.val.factorial : ℝ)*((t-(p+L)+h.val).factorial : ℝ)) := by
 rw [theorem1PsiMatrix_at_zero_eq_finiteMoments (p+L) t L hst (by omega) lambda hnn,
   realPsiZero_ofReal,← Complex.ofRealHom.map_det]
 change ‖((psiZeroRealMatrix (p+L) t L lambda).det : ℂ)‖ = _
 rw [Complex.norm_real,Real.norm_eq_abs]
 have ha := Matrix.abs_det_submatrix_equiv_equiv (psiZeroRowEquiv p L)
   (psiZeroColumnEquiv p L) (psiZeroRealMatrix (p+L) t L lambda)
 rw [← ha,psiZeroRealMatrix_transport p L t hst lambda,Matrix.det_mul_row]
 have hw : 0 ≤ ∏ j : Fin p ⊕ Fin L, psiZeroColumnScale p L t lambda j := by
   apply Finset.prod_nonneg
   intro j _
   cases j with
   | inl h => exact zero_le_one
   | inr j => exact Real.rpow_nonneg (hnn j) _
 have hp : 0 ≤ ∏ j : Fin L, lambda j^p :=
   Finset.prod_nonneg (fun j _ => pow_nonneg (hnn j) p)
 have hg : 0 ≤ ∏ h : Fin p, (h.val.factorial : ℝ)*((t-(p+L)+h.val).factorial : ℝ) := by
   apply Finset.prod_nonneg
   intro h _
   positivity
 rw [abs_mul,abs_of_nonneg hw,mixedNoncentralMomentMatrix_det,
   abs_mul,abs_mul,abs_of_nonneg hp,abs_of_nonneg hg]
 simp only [Fintype.prod_sum_type,psiZeroColumnScale,Finset.prod_const_one,one_mul,
   Matrix.det_vandermonde,abs_prod]
 ring

theorem theorem1PsiMatrix_zero_norm_det_formula (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ) (hnn : ∀ j, 0 ≤ lambda j) :
 ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖ =
   (∏ j : Fin L, Real.rpow (lambda j) (((t-s : ℕ) : ℝ)/2))*
     ((∏ j : Fin L, lambda j^(s-L))*(∏ i : Fin L, ∏ j ∈ Ioi i, |lambda j-lambda i|))*
       (∏ h : Fin (s-L), (h.val.factorial : ℝ)*((t-s+h.val).factorial : ℝ)) := by
 obtain ⟨p,hp⟩ : ∃ p : ℕ, s = p+L := ⟨s-L,(Nat.sub_add_cancel hLs).symm⟩
 subst s
 have hn : p+L-L = p := by omega
 have he : (∏ h : Fin (p+L-L), (h.val.factorial : ℝ)*((t-(p+L)+h.val).factorial : ℝ)) =
     ∏ h : Fin p, (h.val.factorial : ℝ)*((t-(p+L)+h.val).factorial : ℝ) :=
   Fintype.prod_equiv (finCongr hn) _ _ (by intro h; rfl)
 rw [he]
 simpa only [Nat.add_sub_cancel_right] using psi_norm_product_decomposed p L t hst lambda hnn

end
end JinWishart
#print axioms JinWishart.psiZeroRealMatrix_transport
#print axioms JinWishart.theorem1PsiMatrix_zero_norm_det_formula
