import JinWishartFormalization.MixedMinorProduct
import JinWishartFormalization.AveragedCauchyBinet

/-! Codex. Seed 2026102901 exact finite mixed-kernel/fixed-floor controls
precede source. The result is deterministic finite-series algebra only, not
an infinite kernel or the actual Wishart law. [需人工审查] Fin/Sum reindexing
and factorial multiplicity. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

private theorem real_factorial_cauchy_binet_mixed {n N : ℕ}
 (A : Matrix (Fin n) (Fin N) ℝ) (B : Matrix (Fin N) (Fin n) ℝ) :
 (n.factorial : ℝ)*(A*B).det =
   ∑ f : Fin n → Fin N, (A.submatrix id f).det*(B.submatrix f id).det := by
 let AC : Matrix (Fin n) (Fin N) ℂ := A.map Complex.ofRealHom
 let BC : Matrix (Fin N) (Fin n) ℂ := B.map Complex.ofRealHom
 have h := det_mul_rectangular_factorial_sum_functions AC BC
 have hm : AC*BC = Complex.ofRealHom.mapMatrix (A*B) := Matrix.map_mul.symm
 have hA (f : Fin n → Fin N) : AC.submatrix id f =
     Complex.ofRealHom.mapMatrix (A.submatrix id f) := rfl
 have hB (f : Fin n → Fin N) : BC.submatrix f id =
     Complex.ofRealHom.mapMatrix (B.submatrix f id) := rfl
 rw [hm,← Complex.ofRealHom.map_det] at h
 simp only [hA,hB,← Complex.ofRealHom.map_det] at h
 simpa [Complex.mul_re] using congrArg Complex.re h

def finiteMixedKernel (p L N : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) : Matrix (Fin (p+L)) (Fin (p+L)) ℝ :=
 (Matrix.of (fun (i : Fin (p+L)) (m : Fin N) => x i ^ m.val)) *
 (Matrix.of (fun m j => mixedKernelCoefficient p L N lambda w m (finSumFinEquiv.symm j)))

def mixedLowestMinor (p L : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) : ℝ :=
 mixedSelectionMinorProduct p L (p+L) x lambda w (finSumFinEquiv (m := p) (n := L))

theorem mixedLowestMinor_pos (p L : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (hx : StrictMono x)
 (hxp : ∀ i, 0 < x i) (hl : StrictMono lambda) (hlp : ∀ i, 0 < lambda i)
 (hw : ∀ m, 0 < w m) : 0 < mixedLowestMinor p L x lambda w := by
 unfold mixedLowestMinor
 apply mixedSelectionMinorProduct_pos p L (p+L) x lambda w finSumFinEquiv
   finSumFinEquiv.injective ?_ hx hxp hl hlp hw
 intro a
 refine ⟨Sum.inl a, ?_⟩
 simp [finSumFinEquiv_apply_left]

theorem finiteMixedKernel_det_lower_bound (p L N : ℕ) (hN : p+L ≤ N)
 (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ) (w : ℕ → ℝ)
 (hx : StrictMono x) (hxp : ∀ i, 0 < x i) (hl : StrictMono lambda)
 (hlp : ∀ i, 0 < lambda i) (hw : ∀ m, 0 < w m) :
 mixedLowestMinor p L x lambda w ≤ ((p+L).factorial : ℝ) *
   (finiteMixedKernel p L N x lambda w).det := by
 let e := finSumFinEquiv (m := p) (n := L)
 let A : Matrix (Fin (p+L)) (Fin N) ℝ := Matrix.of (fun i m => x i ^ m.val)
 let B : Matrix (Fin N) (Fin (p+L)) ℝ := Matrix.of
   (fun m j => mixedKernelCoefficient p L N lambda w m (e.symm j))
 have hK : finiteMixedKernel p L N x lambda w = A*B := rfl
 rw [hK,real_factorial_cauchy_binet_mixed]
 have hterm (f : Fin (p+L) → Fin N) :
     (A.submatrix id f).det*(B.submatrix f id).det =
       mixedSelectionMinorProduct p L N x lambda w (f ∘ e) := by
   have hA : (Matrix.of (fun i j : Fin p ⊕ Fin L => x (e i) ^ (f (e j)).val)) =
       (A.submatrix id f).submatrix e e := rfl
   have hB : (mixedKernelCoefficient p L N lambda w).submatrix (f ∘ e) id =
       (B.submatrix f id).submatrix e e := by
     ext i j
     simp [B]
   unfold mixedSelectionMinorProduct
   change (A.submatrix id f).det*(B.submatrix f id).det =
     (Matrix.of (fun i j : Fin p ⊕ Fin L => x (e i) ^ (f (e j)).val)).det *
       ((mixedKernelCoefficient p L N lambda w).submatrix (f ∘ e) id).det
   rw [hA,hB,Matrix.det_submatrix_equiv_self,Matrix.det_submatrix_equiv_self]
 have hn (f : Fin (p+L) → Fin N) : 0 ≤
     (A.submatrix id f).det*(B.submatrix f id).det := by
   rw [hterm]
   exact mixedSelectionMinorProduct_nonneg p L N x lambda w (f ∘ e) hx hxp hl hlp hw
 let f0 : Fin (p+L) → Fin N := Fin.castLE hN
 have h0 : (A.submatrix id f0).det*(B.submatrix f0 id).det =
     mixedLowestMinor p L x lambda w := by
   rw [hterm]
   rfl
 rw [← h0]
 exact Finset.single_le_sum (f := fun f : Fin (p+L) → Fin N =>
   (A.submatrix id f).det*(B.submatrix f id).det) (fun f _ => hn f) (Finset.mem_univ f0)

theorem finiteMixedKernel_det_pos (p L N : ℕ) (hN : p+L ≤ N)
 (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ) (w : ℕ → ℝ)
 (hx : StrictMono x) (hxp : ∀ i, 0 < x i) (hl : StrictMono lambda)
 (hlp : ∀ i, 0 < lambda i) (hw : ∀ m, 0 < w m) :
 0 < (finiteMixedKernel p L N x lambda w).det := by
 have hc := mixedLowestMinor_pos p L x lambda w hx hxp hl hlp hw
 have hb := finiteMixedKernel_det_lower_bound p L N hN x lambda w hx hxp hl hlp hw
 have hp : 0 < ((p+L).factorial : ℝ) := by positivity
 exact (mul_pos_iff_of_pos_left hp).mp (lt_of_lt_of_le hc hb)

end
end JinWishart
#print axioms JinWishart.mixedLowestMinor_pos
#print axioms JinWishart.finiteMixedKernel_det_lower_bound
#print axioms JinWishart.finiteMixedKernel_det_pos
