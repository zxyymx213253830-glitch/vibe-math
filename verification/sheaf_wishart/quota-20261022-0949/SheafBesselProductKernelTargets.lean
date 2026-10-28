import JinWishartFormalization.BesselProductKernel
import Lean
open Matrix JinWishart
namespace SheafBesselProductKernel
noncomputable section
def Scalar : Prop := ∀ (q : ℕ) (x lambda : ℝ), 0 ≤ x → 0 ≤ lambda →
 (modifiedBesselI q ((2*Real.sqrt (x*lambda) : ℝ) : ℂ)).re =
 (Real.sqrt x)^q*((Real.sqrt lambda)^q*
   ∑' m : ℕ, x^m*(noncentralKernelSeriesWeight q m*lambda^m))
def MatrixFactor : Prop := ∀ (q n : ℕ) (x lambda : Fin n → ℝ),
 (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ lambda i) →
 besselProductKernel q n x lambda =
 Matrix.of (fun i j => (Real.sqrt (x i))^q*
   ((Real.sqrt (lambda j))^q*noncentralFullSeriesKernel q n x lambda i j))
def Positive : Prop := ∀ (q n : ℕ) (x lambda : Fin n → ℝ),
 StrictMono x → StrictMono lambda → (∀ i, 0 < x i) → (∀ i, 0 < lambda i) →
 0 < (besselProductKernel q n x lambda).det
end
end SheafBesselProductKernel
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.modifiedBesselI_sqrt_product_re,`SheafBesselProductKernel.Scalar),
  (`JinWishart.besselProductKernel_factorization,`SheafBesselProductKernel.MatrixFactor),
  (`JinWishart.besselProductKernel_det_pos,`SheafBesselProductKernel.Positive)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Bessel product kernel literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
