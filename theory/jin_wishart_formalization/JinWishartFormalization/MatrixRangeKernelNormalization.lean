import JinWishartFormalization.RangeKernelNormalization
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Fixed column coordinates B*T=[U,0] with U^H U=I. T is bijective, not
asserted isometric; Gaussian preservation of Z*T is not claimed. Includes
empty/rank-zero factors. Codex. [需人工审查] Subsequent model/law transport. -/
open Matrix Module
namespace JinWishart
noncomputable section

private def splitEuclidean (b c : ℕ) :
    EuclideanSpace ℂ (Fin b ⊕ Fin c) ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin c)) :=
  (WithLp.linearEquiv 2 ℂ _).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin b) (Fin c) ℂ ℂ).trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℂ _).symm (WithLp.linearEquiv 2 ℂ _).symm))

theorem exists_matrix_range_kernel_normalization {p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) :
    ∃ (b c : ℕ) (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ)
      (U : Matrix (Fin p) (Fin b) ℂ),
      b=B.rank ∧ c=finrank ℂ B.toEuclideanLin.ker ∧ b+c=n ∧
      Function.Bijective T.toEuclideanLin ∧ Uᴴ*U=1 ∧ B*T=fromCols U 0 := by
  obtain ⟨b,c,e,f,hb,hc,hf⟩ := exists_linear_range_kernel_normalization B.toEuclideanLin
  let split := splitEuclidean b c
  let T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ :=
    Matrix.toEuclideanLin.symm (split.trans e).toLinearMap
  let U : Matrix (Fin p) (Fin b) ℂ := Matrix.toEuclideanLin.symm f.toLinearMap
  have hT : T.toEuclideanLin=(split.trans e).toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hU : U.toEuclideanLin=f.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hUadj : Uᴴ.toEuclideanLin=f.adjoint := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hU]
  refine ⟨b,c,T,U,?_,hc,?_,?_,?_,?_⟩
  · apply hb.trans
    symm
    convert! B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin p) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis using 1
  · have hd := (split.trans e).finrank_eq
    simpa using hd
  · rw [hT]
    exact (split.trans e).bijective
  · apply Matrix.toEuclideanLin.injective
    have h := f.adjoint_comp_self'
    rw [← hUadj,← hU] at h
    simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same,Matrix.toLpLin_one] using h
  · apply Matrix.toEuclideanLin.injective
    ext u i
    have heT : T.toEuclideanLin u=e (split u) := congrArg (fun L => L u) hT
    have heU : U.toEuclideanLin (split u).1=f (split u).1 := congrArg (fun L => L (split u).1) hU
    have hmul : (B*T).toEuclideanLin u=B.toEuclideanLin (T.toEuclideanLin u) := by
      ext k
      change ((B*T)*ᵥ (⇑u)) k=(B*ᵥ (T*ᵥ (⇑u))) k
      rw [Matrix.mulVec_mulVec]
    calc
      ((B*T).toEuclideanLin u) i=(B.toEuclideanLin (e (split u))) i := by rw [hmul,heT]
      _ = (U.toEuclideanLin (split u).1) i :=
        congrArg (fun w => w i) ((hf (split u).1 (split u).2).trans heU.symm)
      _ = ((fromCols U 0).toEuclideanLin u) i := by
        change (U*ᵥ (⇑(split u).1)) i=(fromCols U 0*ᵥ (⇑u)) i
        rw [fromCols_mulVec,zero_mulVec,add_zero]
        rfl

end
end JinWishart
#print axioms JinWishart.exists_matrix_range_kernel_normalization
