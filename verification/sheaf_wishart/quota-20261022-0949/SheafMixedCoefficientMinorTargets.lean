import JinWishartFormalization.MixedCoefficientMinorZero
import Lean
open Matrix Function JinWishart
namespace SheafMixedCoefficientMinor
noncomputable section
def Missing : Prop := ∀ (p L N : ℕ) (lambda : Fin L → ℝ) (w : ℕ → ℝ)
 (f : (Fin p ⊕ Fin L) → Fin N) (a : Fin p),
 (∀ i, (f i).val ≠ a.val) →
 ((mixedKernelCoefficient p L N lambda w).submatrix f id).det = 0
def Repeated : Prop := ∀ (p L N : ℕ) (lambda : Fin L → ℝ) (w : ℕ → ℝ)
 (f : (Fin p ⊕ Fin L) → Fin N), ¬ Injective f →
 ((mixedKernelCoefficient p L N lambda w).submatrix f id).det = 0
def CanonicalEq : Prop := ∀ (p L : ℕ) (lambda : Fin L → ℝ) (w : ℕ → ℝ),
 (mixedKernelCoefficient p L (p+L) lambda w).submatrix
   (finSumFinEquiv (m := p) (n := L)) id = weightedZeroConfluentVandermonde p L lambda w
def CanonicalPos : Prop := ∀ (p L : ℕ) (lambda : Fin L → ℝ) (w : ℕ → ℝ),
 StrictMono lambda → (∀ j, 0 < lambda j) → (∀ i : Fin L, 0 < w (p+i.val)) →
 0 < ((mixedKernelCoefficient p L (p+L) lambda w).submatrix
   (finSumFinEquiv (m := p) (n := L)) id).det
def OrderedEq : Prop := ∀ (p L N : ℕ) (hpN : p ≤ N) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ) (k : Fin L → Fin N), (∀ i, p ≤ (k i).val) →
 (mixedKernelCoefficient p L N lambda w).submatrix (mixedOrderedSelection p L N hpN k) id =
 weightedGeneralizedConfluent p L (fun i => (k i).val) lambda w
def OrderedPos : Prop := ∀ (p L N : ℕ) (hpN : p ≤ N) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ) (k : Fin L → Fin N), (∀ i, p ≤ (k i).val) → StrictMono k →
 StrictMono lambda → (∀ j, 0 < lambda j) → (∀ i, 0 < w ((k i).val)) →
 0 < ((mixedKernelCoefficient p L N lambda w).submatrix
   (mixedOrderedSelection p L N hpN k) id).det
end
end SheafMixedCoefficientMinor
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.mixedCoefficientMinor_zero_of_missing,`SheafMixedCoefficientMinor.Missing),
  (`JinWishart.mixedCoefficientMinor_zero_of_repeated,`SheafMixedCoefficientMinor.Repeated),
  (`JinWishart.mixedCoefficient_canonical_eq,`SheafMixedCoefficientMinor.CanonicalEq),
  (`JinWishart.mixedCoefficient_canonical_det_pos,`SheafMixedCoefficientMinor.CanonicalPos),
  (`JinWishart.mixedCoefficient_ordered_eq,`SheafMixedCoefficientMinor.OrderedEq),
  (`JinWishart.mixedCoefficient_ordered_det_pos,`SheafMixedCoefficientMinor.OrderedPos)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mixed coefficient minor literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
