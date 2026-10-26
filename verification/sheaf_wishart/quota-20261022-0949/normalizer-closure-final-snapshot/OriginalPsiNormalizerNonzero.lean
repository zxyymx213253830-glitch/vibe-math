import JinWishartFormalization.MixedNoncentralMomentMatrix

/-! Codex. Seed2026102609 exact controls precede source.
Original Psi(0) denominator nonzero for ALL permitted ranks L<=s, positive
pairwise distinct noncentral parameters, including empty and rank-zero cases.
No density, normalization-integral or actual-CDF identification is asserted.
[需人工审查] Original row/column indexing and later paper/model mapping. -/
open Matrix Finset
namespace JinWishart
noncomputable section

private theorem psi_normalizer_decomposed (p L t : ℕ) (hst : p+L ≤ t)
 (lambda : Fin L → ℝ) (hpos : ∀ j, 0 < lambda j) (hinj : Function.Injective lambda) :
 (theorem1PsiMatrix (p+L) t L hst (by omega) lambda 0).det ≠ 0 := by
 let er : (Fin p ⊕ Fin L) ≃ Fin (p+L) := finSumFinEquiv.trans Fin.revPerm
 let ec : (Fin p ⊕ Fin L) ≃ Fin (p+L) :=
   (Equiv.sumComm (Fin p) (Fin L)).trans
     ((Equiv.sumCongr (Equiv.refl (Fin L)) (Fin.revPerm : Equiv.Perm (Fin p))).trans
       ((finSumFinEquiv (m := L) (n := p)).trans (finCongr (Nat.add_comm L p))))
 have hr (i : Fin p ⊕ Fin L) :
   p+L-((er i).val+1) = mixedMomentDegree p L i := by
   change p+L-((Fin.rev (finSumFinEquiv i)).val+1) = _
   rw [Fin.val_rev]
   have hi := (finSumFinEquiv (m := p) (n := L) i).isLt
   unfold mixedMomentDegree
   omega
 have hcl (h : Fin p) : (ec (Sum.inl h)).val = p+L-(h.val+1) := by
   change L+(Fin.rev h).val = _
   rw [Fin.val_rev]
   omega
 have hcr (j : Fin L) : (ec (Sum.inr j)).val = j.val := by rfl
 let M := mixedNoncentralMomentMatrix (t-(p+L)) p L lambda
 let w : Fin p ⊕ Fin L → ℝ := fun j => match j with
   | Sum.inl _ => 1
   | Sum.inr j => Real.rpow (lambda j) (((t-(p+L) : ℕ) : ℝ)/2)
 let B : Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ := Matrix.of (fun i j => w j * M i j)
 have hB : B.det ≠ 0 := by
   change (Matrix.of (fun i j => w j * M i j)).det ≠ 0
   rw [Matrix.det_mul_row]
   apply mul_ne_zero ?_ (mixedNoncentralMomentMatrix_det_ne_zero (t-(p+L)) p L lambda
     (fun j => ne_of_gt (hpos j)) hinj)
   apply Finset.prod_ne_zero_iff.mpr
   intro j _
   cases j with
   | inl h => exact one_ne_zero
   | inr j => exact ne_of_gt (Real.rpow_pos_of_pos (hpos j) _)
 let A := theorem1PsiMatrix (p+L) t L hst (by omega) lambda 0
 have hsub : A.submatrix er ec = Complex.ofRealHom.mapMatrix B := by
   dsimp [A]
   rw [theorem1PsiMatrix_at_zero_eq_finiteMoments (p+L) t L hst (by omega) lambda
     (fun j => le_of_lt (hpos j))]
   ext i j
   change theorem1ZeroMomentMatrix (p+L) t L lambda (er i) (ec j) = ((B i j : ℝ) : ℂ)
   cases j with
   | inl h =>
     have hnot : ¬ (ec (Sum.inl h)).val < L := by rw [hcl]; omega
     have hg : theorem1GammaIndex (p+L) t (er i) (ec (Sum.inl h)) =
         t-(p+L)+mixedMomentDegree p L i+h.val := by
       unfold theorem1GammaIndex
       have hi := (er i).isLt
       have hri := hr i
       rw [hcl]
       omega
     simp [theorem1ZeroMomentMatrix,hnot,hg,B,w,M,mixedNoncentralMomentMatrix]
   | inr j =>
     have hj : (ec (Sum.inr j)).val < L := by rw [hcr]; exact j.isLt
     have he : (⟨(ec (Sum.inr j)).val,hj⟩ : Fin L) = j := Fin.ext (hcr j)
     simp [theorem1ZeroMomentMatrix,hj,he,hr,B,w,M,mixedNoncentralMomentMatrix,
       Complex.ofReal_mul]
 have hmap : (Complex.ofRealHom.mapMatrix B).det ≠ 0 := by
   rw [← Complex.ofRealHom.map_det]
   change (B.det : ℂ) ≠ 0
   exact_mod_cast hB
 have hre : (A.reindex er.symm ec.symm).det ≠ 0 := by
   change (A.submatrix er ec).det ≠ 0
   rw [hsub]
   exact hmap
 rw [Matrix.det_reindex] at hre
 intro hz
 exact hre (by rw [hz,mul_zero])

theorem theorem1PsiMatrix_zero_det_ne_zero (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ) (hpos : ∀ j, 0 < lambda j) (hinj : Function.Injective lambda) :
 (theorem1PsiMatrix s t L hst hLs lambda 0).det ≠ 0 := by
 obtain ⟨p,hp⟩ : ∃ p : ℕ, s = p+L := ⟨s-L,(Nat.sub_add_cancel hLs).symm⟩
 subst s
 exact psi_normalizer_decomposed p L t hst lambda hpos hinj

end
end JinWishart
#print axioms JinWishart.theorem1PsiMatrix_zero_det_ne_zero
