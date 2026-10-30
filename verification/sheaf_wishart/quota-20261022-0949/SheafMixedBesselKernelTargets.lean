import JinWishartFormalization.MixedBesselKernel
import Lean
open Matrix JinWishart
namespace SheafMixedBesselKernel
noncomputable section
def Factor : Prop := ∀ (p L q : ℕ) (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ),
 (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ lambda i) → mixedBesselKernel p L q x lambda =
 Matrix.of (fun i j => (Real.sqrt (x i))^q *
 (mixedBesselColumnFactor p L q lambda j * infiniteMixedKernel p L q x lambda i j))
def Positive : Prop := ∀ (p L q : ℕ) (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ),
 StrictMono x → (∀ i, 0 < x i) → StrictMono lambda → (∀ i, 0 < lambda i) →
 0 < (mixedBesselKernel p L q x lambda).det
end
end SheafMixedBesselKernel
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.mixedBesselKernel_factorization,`SheafMixedBesselKernel.Factor),
 (`JinWishart.mixedBesselKernel_det_pos,`SheafMixedBesselKernel.Positive)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mixed Bessel literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
