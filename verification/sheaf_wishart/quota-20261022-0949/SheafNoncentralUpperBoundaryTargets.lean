import JinWishartFormalization.OriginalNoncentralCandidateUpperBoundary
import Lean
open Matrix Filter JinWishart
open scoped Topology
namespace SheafNoncentralUpperBoundary
noncomputable section
def PsiTail : Prop := ∀ (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ),
 Tendsto (fun x : ℝ => theorem1PsiMatrix s t L hst hLs lambda x) atTop
   (𝓝 (0 : Matrix (Fin s) (Fin s) ℂ))
def XiFull : Prop := ∀ (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ),
 Tendsto (fun x : ℝ => theorem2XiMatrix s t L hst hLs lambda x) atTop
   (𝓝 (theorem1PsiMatrix s t L hst hLs lambda 0))
def MinimumUpper : Prop := ∀ (s t L : ℕ) (hs : 0 < s)
 (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ),
 Tendsto (fun x : ℝ => theorem1CdfCandidate s t L hst hLs lambda x) atTop (𝓝 1)
def MaximumUpper : Prop := ∀ (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ), (∀ j, 0 < lambda j) → Function.Injective lambda →
 Tendsto (fun x : ℝ => theorem2CdfCandidate s t L hst hLs lambda x) atTop (𝓝 1)
end
end SheafNoncentralUpperBoundary
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.theorem1PsiMatrix_tendsto_zero,`SheafNoncentralUpperBoundary.PsiTail),
  (`JinWishart.theorem2XiMatrix_tendsto_full,`SheafNoncentralUpperBoundary.XiFull),
  (`JinWishart.theorem1CdfCandidate_tendsto_one,`SheafNoncentralUpperBoundary.MinimumUpper),
  (`JinWishart.theorem2CdfCandidate_tendsto_one,`SheafNoncentralUpperBoundary.MaximumUpper)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Original noncentral candidate upper boundary literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
