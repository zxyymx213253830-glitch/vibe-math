import JinWishartFormalization.NuttallSeriesTailBridge
import JinWishartFormalization.GammaTailMomentBridge
import JinWishartFormalization.MixedEnsembleProbability
import JinWishartFormalization.OriginalPsiNormalizerProduct

/-! Codex. Seed 2026103006:531 scalar and matrix quadrature controls precede
source. Formula-side paper Psi versus positive-tail candidate moments only.
No actual Wishart spectral law is asserted. [需人工审查] Reindexing, improper
integrals, noncentral parameter ordering and paper conventions. -/
open MeasureTheory Matrix Set
namespace JinWishart
noncomputable section

def mixedCandidateTailMatrix (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ) :
 Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
 Matrix.of (fun i j => ∫ y in Ioi x,
   mixedEnsembleF p L (finSumFinEquiv i) y * mixedEnsembleG p L q lambda (finSumFinEquiv j) y)

def psiTailColumnFactor (p L q : ℕ) (lambda : Fin L → ℝ) : Fin p ⊕ Fin L → ℝ
 | Sum.inl _ => 1
 | Sum.inr j => (Real.sqrt (lambda j))^q * Real.exp (-(lambda j))

theorem mixedCandidateTailMatrix_central (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : ℝ) (hx : 0 ≤ x) (i : Fin p ⊕ Fin L) (a : Fin p) :
 mixedCandidateTailMatrix p L q lambda x i (Sum.inl a) =
   ∫ y in Ioi x, y^(q+mixedMomentDegree p L i+a.val)*Real.exp (-y) := by
 apply setIntegral_congr_fun measurableSet_Ioi
 intro y hy
 have hy0 : 0 < y := lt_of_le_of_lt hx hy
 simp only [mixedCandidateTailMatrix,Matrix.of_apply,mixedEnsembleF,mixedEnsembleG,
   if_pos hy0,Equiv.symm_apply_apply,mixedMomentDegree,pow_add]
 ring

theorem mixedCandidateTailMatrix_noncentral (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : ℝ) (hx : 0 ≤ x) (i : Fin p ⊕ Fin L) (j : Fin L) :
 mixedCandidateTailMatrix p L q lambda x i (Sum.inr j) =
   ∫ y in Ioi x, y^(q+mixedMomentDegree p L i)*Real.exp (-y)*scalarSeriesKernel q (lambda j) y := by
 apply setIntegral_congr_fun measurableSet_Ioi
 intro y hy
 have hy0 : 0 < y := lt_of_le_of_lt hx hy
 simp only [mixedCandidateTailMatrix,Matrix.of_apply,mixedEnsembleF,mixedEnsembleG,
   if_pos hy0,Equiv.symm_apply_apply,mixedMomentDegree,scalarSeriesKernel,pow_add]
 ring

theorem paperPsi_tail_matrix_transport (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (x : ℝ) (hx : 0 ≤ x) :
 (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).submatrix
   (psiZeroRowEquiv p L) (psiZeroColumnEquiv p L) =
 Complex.ofRealHom.mapMatrix (Matrix.of (fun i j =>
   psiTailColumnFactor p L q lambda j * mixedCandidateTailMatrix p L q lambda x i j)) := by
 have hr (i : Fin p ⊕ Fin L) :
   p+L-((psiZeroRowEquiv p L i).val+1) = mixedMomentDegree p L i := by
   change p+L-((Fin.rev (finSumFinEquiv i)).val+1) = _
   rw [Fin.val_rev]
   have hi := (finSumFinEquiv (m := p) (n := L) i).isLt
   unfold mixedMomentDegree
   omega
 have hcl (a : Fin p) : (psiZeroColumnEquiv p L (Sum.inl a)).val = p+L-(a.val+1) := by
   change L+(Fin.rev a).val = _
   rw [Fin.val_rev]
   omega
 have hcr (j : Fin L) : (psiZeroColumnEquiv p L (Sum.inr j)).val = j.val := by rfl
 ext i j
 change theorem1PsiEntry (p+L) (p+L+q) L (by omega) (by omega) lambda
   (psiZeroRowEquiv p L i) (psiZeroColumnEquiv p L j) x =
     ((psiTailColumnFactor p L q lambda j * mixedCandidateTailMatrix p L q lambda x i j : ℝ) : ℂ)
 cases j with
 | inl a =>
   have hnot : ¬ (psiZeroColumnEquiv p L (Sum.inl a)).val < L := by rw [hcl]; omega
   have hg : theorem1GammaIndex (p+L) (p+L+q) (psiZeroRowEquiv p L i)
       (psiZeroColumnEquiv p L (Sum.inl a)) = q+mixedMomentDegree p L i+a.val := by
     unfold theorem1GammaIndex
     have hi := (psiZeroRowEquiv p L i).isLt
     have hri := hr i
     rw [hcl]
     omega
   simp only [theorem1PsiEntry,dif_neg hnot,hg,psiTailColumnFactor,one_mul]
   rw [upperGammaNat_eq_realTailMoment _ x hx,mixedCandidateTailMatrix_central p L q lambda x hx i a]
 | inr j =>
   have hj : (psiZeroColumnEquiv p L (Sum.inr j)).val < L := by rw [hcr]; exact j.isLt
   have he : (⟨(psiZeroColumnEquiv p L (Sum.inr j)).val,hj⟩ : Fin L) = j := Fin.ext (hcr j)
   have ho : theorem1QOrder (p+L) (p+L+q) (psiZeroRowEquiv p L i) =
       q+2*(mixedMomentDegree p L i)+1 := by
     unfold theorem1QOrder
     have hi := (psiZeroRowEquiv p L i).isLt
     have hri := hr i
     omega
   have hpref : ((((2*((psiZeroRowEquiv p L i).val+1) : ℕ) : ℝ) - (p+L) - (p+L+q))/2) =
       -((q : ℝ)/2)-(mixedMomentDegree p L i : ℝ) := by
     have hi : (psiZeroRowEquiv p L i).val+1 ≤ p+L := by have := (psiZeroRowEquiv p L i).isLt; omega
     have hri := hr i
     have hcast := congrArg (fun n : ℕ => (n : ℝ)) hri
     rw [Nat.cast_sub hi] at hcast
     push_cast at hcast ⊢
     linarith
   simp only [theorem1PsiEntry,dif_pos hj,he,ho,psiTailColumnFactor]
   rw [show p+L+q-(p+L)=q by omega]
   push_cast at hpref ⊢
   rw [hpref]
   rw [paperScaled_nuttallQ_series_tail q (mixedMomentDegree p L i) (lambda j) x (hl j) hx,
     mixedCandidateTailMatrix_noncentral p L q lambda x hx i j]
   push_cast
   rfl

end
end JinWishart
#print axioms JinWishart.mixedCandidateTailMatrix_central
#print axioms JinWishart.mixedCandidateTailMatrix_noncentral
#print axioms JinWishart.paperPsi_tail_matrix_transport
