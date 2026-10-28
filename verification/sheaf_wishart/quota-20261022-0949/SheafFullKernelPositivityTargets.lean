import JinWishartFormalization.InfiniteNoncentralKernel
import Lean
open Matrix Filter JinWishart
open scoped Topology
namespace SheafFullKernelPositivity
noncomputable section
def Pair : Prop := ∀ (n : ℕ) (k : Fin n → ℕ) (x y : Fin n → ℝ),
 Function.Injective k → StrictMono x → StrictMono y →
 (∀ i, 0 < x i) → (∀ i, 0 < y i) →
 0 < (Matrix.of (fun i j : Fin n => x i ^ k j)).det *
   (Matrix.of (fun i j : Fin n => y i ^ k j)).det
def WeightedPair : Prop := ∀ (n : ℕ) (k : Fin n → ℕ) (x y w : Fin n → ℝ),
 Function.Injective k → StrictMono x → StrictMono y →
 (∀ i, 0 < x i) → (∀ i, 0 < y i) → (∀ i, 0 < w i) →
 0 < (Matrix.of (fun i j : Fin n => x i ^ k j)).det *
   (Matrix.of (fun i j : Fin n => w i * y j ^ k i)).det
def WeightedNonneg : Prop := ∀ (n : ℕ) (k : Fin n → ℕ) (x y w : Fin n → ℝ),
 StrictMono x → StrictMono y → (∀ i, 0 < x i) → (∀ i, 0 < y i) →
 (∀ i, 0 < w i) →
 0 ≤ (Matrix.of (fun i j : Fin n => x i ^ k j)).det *
   (Matrix.of (fun i j : Fin n => w i * y j ^ k i)).det
def FiniteFloor : Prop := ∀ (q n N : ℕ), n ≤ N → ∀ (x lambda : Fin n → ℝ),
 StrictMono x → StrictMono lambda → (∀ i, 0 < x i) → (∀ i, 0 < lambda i) →
 noncentralKernelLowestMinor q n x lambda ≤
   (n.factorial : ℝ)*(finiteNoncentralFullKernel q n N x lambda).det
def FinitePositive : Prop := ∀ (q n N : ℕ), n ≤ N → ∀ (x lambda : Fin n → ℝ),
 StrictMono x → StrictMono lambda → (∀ i, 0 < x i) → (∀ i, 0 < lambda i) →
 0 < (finiteNoncentralFullKernel q n N x lambda).det
def MatrixLimit : Prop := ∀ (q n : ℕ) (x lambda : Fin n → ℝ),
 (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ lambda i) →
 Tendsto (fun N : ℕ => finiteNoncentralFullKernel q n N x lambda) atTop
   (𝓝 (noncentralFullSeriesKernel q n x lambda))
def InfiniteFloor : Prop := ∀ (q n : ℕ) (x lambda : Fin n → ℝ),
 StrictMono x → StrictMono lambda → (∀ i, 0 < x i) → (∀ i, 0 < lambda i) →
 noncentralKernelLowestMinor q n x lambda ≤
   (n.factorial : ℝ)*(noncentralFullSeriesKernel q n x lambda).det
def InfinitePositive : Prop := ∀ (q n : ℕ) (x lambda : Fin n → ℝ),
 StrictMono x → StrictMono lambda → (∀ i, 0 < x i) → (∀ i, 0 < lambda i) →
 0 < (noncentralFullSeriesKernel q n x lambda).det
end
end SheafFullKernelPositivity
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.generalizedMonomialMinorProduct_pos,`SheafFullKernelPositivity.Pair),
  (`JinWishart.weightedGeneralizedMonomialMinorProduct_pos,`SheafFullKernelPositivity.WeightedPair),
  (`JinWishart.weightedGeneralizedMonomialMinorProduct_nonneg,`SheafFullKernelPositivity.WeightedNonneg),
  (`JinWishart.finiteNoncentralFullKernel_det_lower_bound,`SheafFullKernelPositivity.FiniteFloor),
  (`JinWishart.finiteNoncentralFullKernel_det_pos,`SheafFullKernelPositivity.FinitePositive),
  (`JinWishart.finiteNoncentralFullKernel_tendsto,`SheafFullKernelPositivity.MatrixLimit),
  (`JinWishart.noncentralFullSeriesKernel_det_lower_bound,`SheafFullKernelPositivity.InfiniteFloor),
  (`JinWishart.noncentralFullSeriesKernel_det_pos,`SheafFullKernelPositivity.InfinitePositive)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Full kernel positivity literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
