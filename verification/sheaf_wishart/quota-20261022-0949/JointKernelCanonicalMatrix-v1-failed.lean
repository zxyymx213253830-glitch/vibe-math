import JinWishartFormalization.CompressedJointKernelInjectivity
import JinWishartFormalization.JointKernelCanonicalNormalization

/-! Explicit Sum-indexed matrices for a fixed common-kernel-zero canonical
normal form. Column T is bijective, not asserted isometric. Codex.
[需人工审查] Fin reindexing, actual-source and inverse-moment transport. -/
open Matrix Module
namespace JinWishart
noncomputable section

private def canonicalSplit (b c : ℕ) :
    EuclideanSpace ℂ (Fin b ⊕ Fin c) ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin c)) :=
  (WithLp.linearEquiv 2 ℂ _).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin b) (Fin c) ℂ ℂ).trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℂ _).symm
        (WithLp.linearEquiv 2 ℂ _).symm))

private theorem matrixSingleApply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (j : κ) (i : ι) :
    A.toEuclideanLin (EuclideanSpace.single j 1) i=A i j := by
  change (A*ᵥ Pi.single j 1) i=A i j
  rw [Matrix.mulVec_single_one]
  rfl

theorem exists_joint_kernel_canonical_matrix {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hjoint : Function.Injective (B.toEuclideanLin.prod M.toEuclideanLin)) :
    ∃ (b c a : ℕ) (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ)
      (U : Matrix (Fin p) (Fin b) ℂ)
      (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
      (N : Matrix (Fin c) (Fin c) ℂ)
      (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ),
      b=B.rank ∧ c=finrank ℂ B.toEuclideanLin.ker ∧ b+c=n ∧ a+c=m ∧
      Function.Bijective T.toEuclideanLin ∧ Uᴴ*U=1 ∧ B*T=fromCols U 0 ∧
      Function.Bijective N.toEuclideanLin ∧
      (fromBlocks A 0 H N).toEuclideanLin=
        V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin := by
  obtain ⟨b,c,a,e,f,V,g,hb,hc,hbc,hac,hB,hM⟩ :=
    exists_joint_kernel_canonical_normalization B.toEuclideanLin M.toEuclideanLin hjoint
  let split := canonicalSplit b c
  let T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ := Matrix.toEuclideanLin.symm (split.trans e).toLinearMap
  let U : Matrix (Fin p) (Fin b) ℂ := Matrix.toEuclideanLin.symm f.toLinearMap
  let N : Matrix (Fin c) (Fin c) ℂ := Matrix.toEuclideanLin.symm g.toLinearMap
  have hT : T.toEuclideanLin=(split.trans e).toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hU : U.toEuclideanLin=f.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hN : N.toEuclideanLin=g.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  let D : Matrix (Fin a ⊕ Fin c) (Fin b ⊕ Fin c) ℂ :=
    Matrix.toEuclideanLin.symm (V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin)
  have hD : D.toEuclideanLin=V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin :=
    Matrix.toEuclideanLin.apply_symm_apply _
  have hBT : B*T=fromCols U 0 := by
    apply Matrix.toEuclideanLin.injective
    ext w i
    have hmul : (B*T).toEuclideanLin w=B.toEuclideanLin (T.toEuclideanLin w) := by
      ext k
      change ((B*T)*ᵥ (⇑w)) k=(B*ᵥ (T*ᵥ (⇑w))) k
      rw [Matrix.mulVec_mulVec]
    rw [hmul,hT]
    change B.toEuclideanLin (e (split w)) i=_
    rw [hB (split w).1 (split w).2]
    change f (split w).1 i=((fromCols U 0).toEuclideanLin w) i
    rw [← hU]
    change (U*ᵥ (⇑(split w).1)) i=(fromCols U 0*ᵥ (⇑w)) i
    rw [fromCols_mulVec,zero_mulVec,add_zero]
    rfl
  have hDapply (w : EuclideanSpace ℂ (Fin b ⊕ Fin c)) :
      D.toEuclideanLin w=V (M.toEuclideanLin (e (split w))) := by
    rw [hD]
    change V ((M*T).toEuclideanLin w)=_
    congr 1
    have hmul : (M*T).toEuclideanLin w=M.toEuclideanLin (T.toEuclideanLin w) := by
      ext k
      change ((M*T)*ᵥ (⇑w)) k=(M*ᵥ (T*ᵥ (⇑w))) k
      rw [Matrix.mulVec_mulVec]
    rw [hmul,hT]
    rfl
  have hright (v : EuclideanSpace ℂ (Fin c)) :
      D.toEuclideanLin (WithLp.toLp 2 (Sum.elim (fun _ : Fin b => (0 : ℂ)) (fun j => v j)))=
        WithLp.toLp 2 (Sum.elim (fun _ : Fin a => (0 : ℂ)) (fun j => g v j)) := by
    rw [hDapply]
    change V (M.toEuclideanLin (e (0,v)))=_
    simpa using hM 0 v
  have hemb (j : Fin c) :
      WithLp.toLp 2 (Sum.elim (fun _ : Fin b => (0 : ℂ))
        (fun k => EuclideanSpace.single j (1 : ℂ) k))=
        EuclideanSpace.single (Sum.inr j) (1 : ℂ) := by
    ext i
    rcases i with i | i <;> simp [PiLp.single_apply]
  have hcol (i : Fin a ⊕ Fin c) (j : Fin c) :
      D i (Sum.inr j)=
        (WithLp.toLp 2 (Sum.elim (fun _ : Fin a => (0 : ℂ))
          (fun k => g (EuclideanSpace.single j 1) k))) i := by
    have h := congrArg (fun z => z i) (hright (EuclideanSpace.single j 1))
    rw [hemb,matrixSingleApply] at h
    exact h
  have hz : D.toBlocks₁₂=0 := by
    ext i j
    exact hcol (Sum.inl i) j
  have hdn : D.toBlocks₂₂=N := by
    ext i j
    change D (Sum.inr i) (Sum.inr j)=N i j
    calc
      _=g (EuclideanSpace.single j 1) i := hcol (Sum.inr i) j
      _=N.toEuclideanLin (EuclideanSpace.single j 1) i :=
        congrArg (fun L => L (EuclideanSpace.single j 1) i) hN.symm
      _=N i j := matrixSingleApply N j i
  have hblock : fromBlocks D.toBlocks₁₁ 0 D.toBlocks₂₁ N=D := by
    rw [← hz,← hdn]
    exact Matrix.fromBlocks_toBlocks D
  refine ⟨b,c,a,T,U,V,N,D.toBlocks₁₁,D.toBlocks₂₁,?_,hc,?_,?_,?_,?_,hBT,?_,?_⟩
  · apply hb.trans
    symm
    convert! B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin p) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis using 1
  · simpa using hbc
  · simpa using hac
  · rw [hT]
    exact (split.trans e).bijective
  · have hUadj : Uᴴ.toEuclideanLin=f.adjoint := by
      rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hU]
    apply Matrix.toEuclideanLin.injective
    have h := f.adjoint_comp_self'
    rw [← hUadj,← hU] at h
    simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same,Matrix.toLpLin_one] using h
  · rw [hN]
    exact g.bijective
  · rw [hblock]
    exact hD

end
end JinWishart
#print axioms JinWishart.exists_joint_kernel_canonical_matrix
