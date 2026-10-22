import JinWishartFormalization.CanonicalSumNoiseBlockLaw
import Lean
open Matrix Module MeasureTheory ProbabilityTheory JinWishart
namespace SheafCanonicalMatrix
noncomputable section
def CompressionTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin r) ℂ)
    (hr : r=(Matrix.fromRows B M).rank)
    (hB : B*C*Cᴴ=B) (hM : M*C*Cᴴ=M),
    Function.Injective ((B*C).toEuclideanLin.prod (M*C).toEuclideanLin)
def MatrixTarget : Prop := ∀ {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hjoint : Function.Injective (B.toEuclideanLin.prod M.toEuclideanLin)),
    ∃ (b c a : ℕ) (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ)
      (U : Matrix (Fin p) (Fin b) ℂ)
      (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
      (N : Matrix (Fin c) (Fin c) ℂ)
      (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ),
      b=B.rank ∧ c=finrank ℂ B.toEuclideanLin.ker ∧ b+c=n ∧ a+c=m ∧
      Function.Bijective T.toEuclideanLin ∧ Uᴴ*U=1 ∧ B*T=fromCols U 0 ∧
      Function.Bijective N.toEuclideanLin ∧
      (fromBlocks A 0 H N).toEuclideanLin=
        V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin
def LawTarget : Prop := ∀ {m p b a c : ℕ}
    (U : Matrix (Fin p) (Fin b) ℂ) (hU : Uᴴ*U=1)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ),
    (stdGaussian (ComplexSample (m := m) (n := p))).map (fun z =>
      ((fun i j => V (complexMatrixColumn (complexSampleMatrix z*U) j) (Sum.inl i)+A i j),
       (fun i j => V (complexMatrixColumn (complexSampleMatrix z*U) j) (Sum.inr i)+H i j)))=
      (complexGaussianMatrixLaw A).prod (complexGaussianMatrixLaw H)
end
end SheafCanonicalMatrix
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.correlated_fixed_compression_joint_injective,`SheafCanonicalMatrix.CompressionTarget),
 (`JinWishart.exists_joint_kernel_canonical_matrix,`SheafCanonicalMatrix.MatrixTarget),
 (`JinWishart.actual_sum_isometric_noise_block_law,`SheafCanonicalMatrix.LawTarget) ] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF canonical matrix/model target differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
