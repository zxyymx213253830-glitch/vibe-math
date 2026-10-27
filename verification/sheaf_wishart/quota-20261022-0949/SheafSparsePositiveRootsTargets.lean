import JinWishartFormalization.SparsePositiveRoots
import Lean
open Polynomial Matrix JinWishart
namespace SheafSparsePositiveRoots
noncomputable section
def SignSupport : Prop := ∀ (P : ℝ[X]), P ≠ 0 → P.signVariations < P.support.card
def CountSupport : Prop := ∀ (P : ℝ[X]), P ≠ 0 →
 P.roots.countP (0 < ·) < P.support.card
def SetSupport : Prop := ∀ (P : ℝ[X]), P ≠ 0 → ∀ (S : Finset ℝ),
 (∀ x ∈ S, 0 < x) → (∀ x ∈ S, P.eval x = 0) → S.card < P.support.card
def MatrixNonzero : Prop := ∀ (n : ℕ) (k : Fin n → ℕ) (x : Fin n → ℝ),
 Function.Injective k → Function.Injective x → (∀ i, 0 < x i) →
 (Matrix.of (fun i j : Fin n => x i ^ k j)).det ≠ 0
end
end SheafSparsePositiveRoots
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.polynomial_signVariations_lt_support,`SheafSparsePositiveRoots.SignSupport),
  (`JinWishart.polynomial_positive_roots_lt_support,`SheafSparsePositiveRoots.CountSupport),
  (`JinWishart.positive_root_set_card_lt_support,`SheafSparsePositiveRoots.SetSupport),
  (`JinWishart.generalizedMonomialVandermonde_det_ne_zero,`SheafSparsePositiveRoots.MatrixNonzero)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Sparse positive roots literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
