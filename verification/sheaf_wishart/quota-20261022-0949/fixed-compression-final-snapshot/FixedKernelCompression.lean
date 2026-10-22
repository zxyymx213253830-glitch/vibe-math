import JinWishartFormalization.GramMinimumLeftComparison
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Fixed orthonormal compression onto the complement of a linear kernel.
Includes rank zero. Deterministic Codex proofs, no Gaussian-law claims.
[需人工审查] Subsequent nonzero-spectrum and actual-law transport. -/
open Matrix Module
namespace JinWishart
noncomputable section

theorem exists_linear_isometric_kernel_compression
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) :
    ∃ (r : ℕ) (f : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] E),
      r=finrank ℂ T.range ∧ (T.comp f.toLinearMap).comp f.adjoint=T := by
  let K := T.kerᗮ
  let r := finrank ℂ K
  let e : EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] K :=
    (stdOrthonormalBasis ℂ K).repr.symm
  let f : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] E := K.subtypeₗᵢ.comp e.toLinearIsometry
  have hRange : f.toLinearMap.range=K := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact (e u).property
    · intro hx
      obtain ⟨u,hu⟩ := e.surjective ⟨x,hx⟩
      exact ⟨u,congrArg Subtype.val hu⟩
  refine ⟨r,f,?_,?_⟩
  · change finrank ℂ T.kerᗮ=finrank ℂ T.range
    rw [T.orthogonal_ker,T.finrank_range_adjoint]
  · ext x
    have horth : x-f (f.adjoint x) ∈ f.toLinearMap.rangeᗮ := by
      rw [LinearMap.orthogonal_range]
      change f.adjoint (x-f (f.adjoint x))=0
      rw [map_sub]
      have h := congrArg (fun L => L (f.adjoint x)) f.adjoint_comp_self'
      exact sub_eq_zero.mpr h.symm
    have hk : x-f (f.adjoint x) ∈ T.ker := by
      simpa only [hRange,K,Submodule.orthogonal_orthogonal] using horth
    have ht : T x-T (f (f.adjoint x))=0 := by
      simpa only [LinearMap.mem_ker,map_sub] using hk
    exact (sub_eq_zero.mp ht).symm

theorem exists_matrix_fixed_kernel_compression {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (A : Matrix ι (Fin n) ℂ) :
    ∃ (r : ℕ) (C : Matrix (Fin n) (Fin r) ℂ),
      r=A.rank ∧ Cᴴ*C=1 ∧ A*C*Cᴴ=A := by
  obtain ⟨r,f,hr,hf⟩ := exists_linear_isometric_kernel_compression A.toEuclideanLin
  let C : Matrix (Fin n) (Fin r) ℂ := Matrix.toEuclideanLin.symm f.toLinearMap
  have hC : C.toEuclideanLin=f.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hCadj : Cᴴ.toEuclideanLin=f.adjoint := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hC]
  refine ⟨r,C,?_,?_,?_⟩
  · apply hr.trans
    symm
    convert! A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun ι ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis using 1
  · apply Matrix.toEuclideanLin.injective
    have h := f.adjoint_comp_self'
    rw [← hCadj,← hC] at h
    simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same,Matrix.toLpLin_one] using h
  · apply Matrix.toEuclideanLin.injective
    rw [← hCadj,← hC] at hf
    simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same] using hf

end
end JinWishart
#print axioms JinWishart.exists_linear_isometric_kernel_compression
#print axioms JinWishart.exists_matrix_fixed_kernel_compression
