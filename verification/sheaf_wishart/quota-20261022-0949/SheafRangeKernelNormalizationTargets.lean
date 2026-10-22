import JinWishartFormalization.MatrixRangeKernelNormalization
import Lean
open Matrix Module
namespace SheafRangeKernel
noncomputable section
def LinearTarget : Prop := ∀ {E F : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
 [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
 (T : E →ₗ[ℂ] F),
 ∃ (b c : ℕ) (e : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin c)) ≃ₗ[ℂ] E)
 (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] F),
 b=finrank ℂ T.range ∧ c=finrank ℂ T.ker ∧ ∀ u v,T (e (u,v))=U u
def MatrixTarget : Prop := ∀ {p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ),
 ∃ (b c : ℕ) (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ),
 b=B.rank ∧ c=finrank ℂ B.toEuclideanLin.ker ∧ b+c=n ∧
 Function.Bijective T.toEuclideanLin ∧ Uᴴ*U=1 ∧ B*T=fromCols U 0
end
end SheafRangeKernel
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.exists_linear_range_kernel_normalization,`SheafRangeKernel.LinearTarget),
 (`JinWishart.exists_matrix_range_kernel_normalization,`SheafRangeKernel.MatrixTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
