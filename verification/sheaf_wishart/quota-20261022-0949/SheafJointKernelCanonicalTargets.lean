import JinWishartFormalization.JointKernelCanonicalNormalization
import Lean
open Module
namespace SheafJointKernel
noncomputable section
def Target : Prop := ∀
    {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [FiniteDimensional ℂ G] (T : E →ₗ[ℂ] F) (M : E →ₗ[ℂ] G)
    (hjoint : Function.Injective (T.prod M)),
    ∃ (b c a : ℕ)
      (e : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin c)) ≃ₗ[ℂ] E)
      (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] F)
      (V : G ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
      (N : EuclideanSpace ℂ (Fin c) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin c)),
      b=finrank ℂ T.range ∧ c=finrank ℂ T.ker ∧ b+c=finrank ℂ E ∧
      a+c=finrank ℂ G ∧
      (∀ u v,T (e (u,v))=U u) ∧
      ∀ u v,V (M (e (u,v)))=V (M (e (u,0)))+
        WithLp.toLp 2 (Sum.elim (fun _ : Fin a => (0 : ℂ)) (fun j => N v j))
end
end SheafJointKernel
open Lean Meta in
#eval show MetaM Unit from do
 let actualType ← inferType (← mkConstWithFreshMVarLevels `JinWishart.exists_joint_kernel_canonical_normalization)
 let expectedType ← whnf (← mkConstWithFreshMVarLevels `SheafJointKernel.Target)
 unless ← isDefEq actualType expectedType do
  throwError "SHEAF joint kernel canonical type differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
