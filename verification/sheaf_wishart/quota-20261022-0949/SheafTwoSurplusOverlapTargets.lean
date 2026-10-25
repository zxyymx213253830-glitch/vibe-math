import JinWishartFormalization.TwoSurplusOverlapKernel
import Lean
open JinWishart
namespace SheafTwoSurplusOverlap
noncomputable section
def Moment : Prop := ∀ (n : ℕ) (S T : Finset (Fin n)),
 centralMixedMinorMoment n S T 1 1 =
 ((n.factorial : ℝ)*((n+1).factorial : ℝ))/
 (((n-(S ∩ T).card+1 : ℕ) : ℝ)*((n-S.card).factorial : ℝ)*((n-T.card).factorial : ℝ))
def Kernel : Prop := ∀ (n : ℕ) (x : ℝ),
 twoExtraRowMinimumPolynomial n x = ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
 x^(n-S.card+(n-T.card))/
 (((n-(S ∩ T).card+1 : ℕ) : ℝ)*((n-S.card).factorial : ℝ)*((n-T.card).factorial : ℝ))
end
end SheafTwoSurplusOverlap
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.centralMixedMinorMoment_first_product_closed,`SheafTwoSurplusOverlap.Moment),
 (`JinWishart.twoExtraRowMinimumPolynomial_eq_overlapKernel,`SheafTwoSurplusOverlap.Kernel)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Overlap kernel literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
