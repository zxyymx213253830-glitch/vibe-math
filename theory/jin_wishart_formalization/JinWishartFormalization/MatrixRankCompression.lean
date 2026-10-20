import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Basic.Complex.Basic

/-! A rank-sized square compression with value one, without selecting coordinate minors.
Codex; pure finite-dimensional linear algebra, including rank zero.
-/
open Matrix Module
namespace JinWishart
noncomputable section

theorem matrix_rank_compression {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (L : Matrix (Fin X.rank) (Fin m) ℂ) (H : Matrix (Fin n) (Fin X.rank) ℂ),
      L*X*H=1 := by
  classical
  let R := LinearMap.range X.mulVecLin
  let e : R ≃ₗ[ℂ] (Fin X.rank → ℂ) := (Module.finBasis ℂ R).equivFun
  obtain ⟨s,hs⟩ := X.mulVecLin.rangeRestrict.exists_rightInverse_of_surjective
    X.mulVecLin.range_rangeRestrict
  obtain ⟨l,hl⟩ := e.toLinearMap.exists_extend
  let h := s.comp e.symm.toLinearMap
  have he : (l.comp X.mulVecLin).comp h=LinearMap.id := by
    apply LinearMap.ext
    intro v
    have hv := LinearMap.congr_fun hs (e.symm v)
    have hx : X.mulVecLin (s (e.symm v))=(e.symm v : Fin m → ℂ) := congrArg Subtype.val hv
    have hv' := LinearMap.congr_fun hl (e.symm v)
    change l (X.mulVecLin (s (e.symm v)))=v
    rw [hx]
    simpa using hv'
  refine ⟨LinearMap.toMatrix' l,LinearMap.toMatrix' h,?_⟩
  have ht := congrArg LinearMap.toMatrix' he
  simpa only [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id,
    ← Matrix.toLin'_apply',LinearMap.toMatrix'_toLin'] using ht

end
end JinWishart
#print axioms JinWishart.matrix_rank_compression
