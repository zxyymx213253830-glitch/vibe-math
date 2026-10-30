import JinWishartFormalization.MixedEnsembleSign
import Lean
open Matrix JinWishart
namespace SheafMixedEnsembleSign
noncomputable section
def Factor : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : Fin (p+L) → ℝ),
 (∀ i, 0 < x i) →
 determinantProduct (mixedEnsembleF p L) (mixedEnsembleG p L q lambda) x =
 (∏ j : Fin (p+L), Real.exp (-(x j))*x j^q)*mixedSeriesNumerator p L q lambda x
def Nonnegative : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ),
 StrictMono lambda → (∀ i, 0 < lambda i) → ∀ x : Fin (p+L) → ℝ,
 0 ≤ determinantProduct (mixedEnsembleF p L) (mixedEnsembleG p L q lambda) x
end
end SheafMixedEnsembleSign
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.mixedDeterminantProduct_eq,`SheafMixedEnsembleSign.Factor),
 (`JinWishart.mixedDeterminantProduct_nonneg,`SheafMixedEnsembleSign.Nonnegative)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mixed ensemble sign literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
