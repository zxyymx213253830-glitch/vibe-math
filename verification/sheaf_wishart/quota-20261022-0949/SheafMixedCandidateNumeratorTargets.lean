import JinWishartFormalization.MixedCandidateNumerator
import Lean
open Matrix Function JinWishart
namespace SheafMixedCandidateNumerator
noncomputable section
def Symmetric : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : Fin (p+L) → ℝ) (σ : Equiv.Perm (Fin (p+L))),
 mixedSeriesNumerator p L q lambda (fun i => x (σ i)) = mixedSeriesNumerator p L q lambda x
def Positive : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : Fin (p+L) → ℝ),
 StrictMono lambda → (∀ i, 0 < lambda i) → Injective x → (∀ i, 0 < x i) →
 0 < mixedSeriesNumerator p L q lambda x
def Nonnegative : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : Fin (p+L) → ℝ),
 StrictMono lambda → (∀ i, 0 < lambda i) → (∀ i, 0 < x i) →
 0 ≤ mixedSeriesNumerator p L q lambda x
end
end SheafMixedCandidateNumerator
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.mixedSeriesNumerator_permute,`SheafMixedCandidateNumerator.Symmetric),
 (`JinWishart.mixedSeriesNumerator_pos,`SheafMixedCandidateNumerator.Positive),
 (`JinWishart.mixedSeriesNumerator_nonneg,`SheafMixedCandidateNumerator.Nonnegative)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mixed numerator literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
