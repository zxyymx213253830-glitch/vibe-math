import JinWishartFormalization.FullRankCandidateNumerator
import Lean
open Matrix JinWishart
namespace SheafFullRankCandidateNumerator
noncomputable section
def Symmetric : Prop := ∀ (q n : ℕ) (lambda x : Fin n → ℝ)
 (σ : Equiv.Perm (Fin n)),
 fullRankSeriesNumerator q n lambda (fun i => x (σ i)) =
   fullRankSeriesNumerator q n lambda x
def Positive : Prop := ∀ (q n : ℕ) (lambda x : Fin n → ℝ),
 StrictMono lambda → (∀ i, 0 < lambda i) → Function.Injective x →
 (∀ i, 0 < x i) → 0 < fullRankSeriesNumerator q n lambda x
def Nonnegative : Prop := ∀ (q n : ℕ) (lambda x : Fin n → ℝ),
 StrictMono lambda → (∀ i, 0 < lambda i) → (∀ i, 0 < x i) →
 0 ≤ fullRankSeriesNumerator q n lambda x
end
end SheafFullRankCandidateNumerator
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.fullRankSeriesNumerator_permute,`SheafFullRankCandidateNumerator.Symmetric),
  (`JinWishart.fullRankSeriesNumerator_pos,`SheafFullRankCandidateNumerator.Positive),
  (`JinWishart.fullRankSeriesNumerator_nonneg,`SheafFullRankCandidateNumerator.Nonnegative)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Full rank numerator literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
