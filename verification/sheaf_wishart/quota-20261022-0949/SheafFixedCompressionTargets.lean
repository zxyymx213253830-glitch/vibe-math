import JinWishartFormalization.CorrelatedFixedKernelCompression
import Lean
open Matrix Module
namespace SheafFixedCompression
noncomputable section
def LinearCompression : Prop := ∀ {E F : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
 [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
 (T : E →ₗ[ℂ] F), ∃ (r : ℕ) (f : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] E),
 r=finrank ℂ T.range ∧ (T.comp f.toLinearMap).comp f.adjoint=T
def MatrixCompression : Prop := ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
 {n : ℕ} (A : Matrix ι (Fin n) ℂ), ∃ (r : ℕ) (C : Matrix (Fin n) (Fin r) ℂ),
 r=A.rank ∧ Cᴴ*C=1 ∧ A*C*Cᴴ=A
def FixedModelCompression : Prop := ∀ {m p n : ℕ}
 (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 ∃ (r : ℕ) (C : Matrix (Fin n) (Fin r) ℂ),
 r=(Matrix.fromRows B M).rank ∧ Cᴴ*C=1 ∧ B*C*Cᴴ=B ∧ M*C*Cᴴ=M ∧
 ∀ Z : Matrix (Fin m) (Fin p) ℂ,
 (Z*B+M)*C*Cᴴ=Z*B+M ∧
 ((Z*B+M)*C)*((Z*B+M)*C)ᴴ=(Z*B+M)*(Z*B+M)ᴴ
end
end SheafFixedCompression
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.exists_linear_isometric_kernel_compression,`SheafFixedCompression.LinearCompression),
 (`JinWishart.exists_matrix_fixed_kernel_compression,`SheafFixedCompression.MatrixCompression),
 (`JinWishart.exists_correlated_fixed_kernel_compression,`SheafFixedCompression.FixedModelCompression)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
