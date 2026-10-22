import JinWishartFormalization.RowSubspaceNormalization
import Lean
open Module
namespace SheafRowSubspace
noncomputable section
def Target : Prop := ∀
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (L : E →ₗ[ℂ] F) (hL : Function.Injective L),
    ∃ (a r : ℕ) (V : F ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin r))
      (N : E ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)),
      r=finrank ℂ E ∧ a+r=finrank ℂ F ∧
      ∀ x,V (L x)=WithLp.toLp 2 (Sum.elim (fun _ : Fin a => (0 : ℂ)) (fun j => N x j))
end
end SheafRowSubspace
open Lean Meta in
#eval show MetaM Unit from do
 let actualType ← inferType (← mkConstWithFreshMVarLevels `JinWishart.exists_injective_row_subspace_normalization)
 let expectedType ← whnf (← mkConstWithFreshMVarLevels `SheafRowSubspace.Target)
 unless ← isDefEq actualType expectedType do
  throwError "SHEAF row normalization target differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
