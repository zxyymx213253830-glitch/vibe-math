import JinWishartFormalization.MixedLaplaceExponent
import Lean
open Matrix Finset JinWishart
namespace SheafMixedLaplaceExponent
def Tri : Prop := ∀ n : ℕ, 2*triangularIndexSum n+n = n*n
def Identity : Prop := ∀ p L q : ℕ,
 (∑ i : Fin (p+L), (q+i.val+1)) +
 (∑ a : Fin p, a.val) + L*p + (∑ j : Fin L, j.val) = (p+L)*(p+L+q)
def Vandermonde : Prop := ∀ (L : ℕ) (lambda : Fin L → ℝ) (c : ℝ),
 (Matrix.vandermonde (fun i => lambda i/c)).det =
 (∏ j : Fin L, (c^j.val)⁻¹) * (Matrix.vandermonde lambda).det
def Mixed : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (c : ℝ),
 (mixedNoncentralMomentMatrix q p L (fun b => lambda b/c)).det =
 (∏ j : Fin L, (c^(p+j.val))⁻¹) * (mixedNoncentralMomentMatrix q p L lambda).det
def Powers : Prop := ∀ (p L q : ℕ) (c : ℝ),
 (∏ i : Fin (p+L), (c^(q+i.val+1))⁻¹) *
 (∏ a : Fin p, (c^a.val)⁻¹) *
 (∏ j : Fin L, (c^(p+j.val))⁻¹) = (c^((p+L)*(p+L+q)))⁻¹
end SheafMixedLaplaceExponent
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.triangularIndexSum_double,`SheafMixedLaplaceExponent.Tri),
 (`JinWishart.mixedLaplaceExponent_identity,`SheafMixedLaplaceExponent.Identity),
 (`JinWishart.vandermonde_det_div_scale,`SheafMixedLaplaceExponent.Vandermonde),
 (`JinWishart.mixedNoncentralMomentMatrix_det_div_scale,`SheafMixedLaplaceExponent.Mixed),
 (`JinWishart.mixedLaplace_power_product,`SheafMixedLaplaceExponent.Powers)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mixed Laplace exponent literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
