import JinWishartFormalization.InfiniteMixedNoncentralKernel
import Lean
open Matrix Function Filter JinWishart
open scoped Topology
namespace SheafMixedKernelClosure
noncomputable section
def DegreeMono : Prop := ∀ (p L N : ℕ) (k : Fin L → Fin N),
 (∀ i, p ≤ (k i).val) → StrictMono k → StrictMono (mixedOrderedDegree p L N k)
def DegreeSelection : Prop := ∀ (p L N : ℕ) (hpN : p ≤ N) (k : Fin L → Fin N)
 (i : Fin p ⊕ Fin L), mixedOrderedDegree p L N k (finSumFinEquiv i) =
 (mixedOrderedSelection p L N hpN k i).val
def OrderedMinor : Prop := ∀ (p L N : ℕ) (hpN : p ≤ N) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (k : Fin L → Fin N),
 (∀ i, p ≤ (k i).val) → StrictMono k → StrictMono x → (∀ i, 0 < x i) →
 StrictMono lambda → (∀ i, 0 < lambda i) → (∀ i, 0 < w ((k i).val)) →
 0 < (Matrix.of (fun i j : Fin p ⊕ Fin L =>
  x (finSumFinEquiv i) ^ (mixedOrderedSelection p L N hpN k j).val)).det *
 ((mixedKernelCoefficient p L N lambda w).submatrix (mixedOrderedSelection p L N hpN k) id).det
def IndexLe : Prop := ∀ (n : ℕ) (g : Fin n → ℕ), StrictMono g → ∀ i, i.val ≤ g i
def Prefix : Prop := ∀ (p L : ℕ) (g : Fin (p+L) → ℕ), StrictMono g →
 (∀ a : Fin p, ∃ i, g i = a.val) → ∀ a : Fin p, g (Fin.castAdd L a) = a.val
def Tail : Prop := ∀ (p L : ℕ) (g : Fin (p+L) → ℕ), StrictMono g →
 ∀ i : Fin L, p ≤ g (Fin.natAdd p i)
def Sorted : Prop := ∀ (p L N : ℕ) (f : (Fin p ⊕ Fin L) → Fin N), Injective f →
 (∀ a : Fin p, ∃ i, (f i).val = a.val) →
 ∃ (hpN : p ≤ N) (k : Fin L → Fin N) (σ : Equiv.Perm (Fin p ⊕ Fin L)),
 (∀ i, p ≤ (k i).val) ∧ StrictMono k ∧ ∀ i, f i = mixedOrderedSelection p L N hpN k (σ i)
def MinorPos : Prop := ∀ (p L N : ℕ) (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ) (f : (Fin p ⊕ Fin L) → Fin N), Injective f →
 (∀ a : Fin p, ∃ i, (f i).val = a.val) → StrictMono x → (∀ i, 0 < x i) →
 StrictMono lambda → (∀ j, 0 < lambda j) → (∀ m, 0 < w m) →
 0 < mixedSelectionMinorProduct p L N x lambda w f
def MinorNonneg : Prop := ∀ (p L N : ℕ) (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ) (f : (Fin p ⊕ Fin L) → Fin N), StrictMono x → (∀ i, 0 < x i) →
 StrictMono lambda → (∀ j, 0 < lambda j) → (∀ m, 0 < w m) →
 0 ≤ mixedSelectionMinorProduct p L N x lambda w f
def LowestPos : Prop := ∀ (p L : ℕ) (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ), StrictMono x → (∀ i, 0 < x i) → StrictMono lambda →
 (∀ i, 0 < lambda i) → (∀ m, 0 < w m) → 0 < mixedLowestMinor p L x lambda w
def FiniteFloor : Prop := ∀ (p L N : ℕ), p+L ≤ N → ∀ (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ), StrictMono x → (∀ i, 0 < x i) →
 StrictMono lambda → (∀ i, 0 < lambda i) → (∀ m, 0 < w m) →
 mixedLowestMinor p L x lambda w ≤ ((p+L).factorial : ℝ)*(finiteMixedKernel p L N x lambda w).det
def FinitePos : Prop := ∀ (p L N : ℕ), p+L ≤ N → ∀ (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ), StrictMono x → (∀ i, 0 < x i) →
 StrictMono lambda → (∀ i, 0 < lambda i) → (∀ m, 0 < w m) →
 0 < (finiteMixedKernel p L N x lambda w).det
def Limit : Prop := ∀ (p L q : ℕ) (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ),
 (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ lambda i) →
 Tendsto (fun N : ℕ => finiteMixedKernel p L N x lambda (noncentralKernelSeriesWeight q))
 atTop (𝓝 (infiniteMixedKernel p L q x lambda))
def InfiniteFloor : Prop := ∀ (p L q : ℕ) (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ),
 StrictMono x → (∀ i, 0 < x i) → StrictMono lambda → (∀ i, 0 < lambda i) →
 mixedLowestMinor p L x lambda (noncentralKernelSeriesWeight q) ≤
 ((p+L).factorial : ℝ)*(infiniteMixedKernel p L q x lambda).det
def InfinitePos : Prop := ∀ (p L q : ℕ) (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ),
 StrictMono x → (∀ i, 0 < x i) → StrictMono lambda → (∀ i, 0 < lambda i) →
 0 < (infiniteMixedKernel p L q x lambda).det
end
end SheafMixedKernelClosure
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.mixedOrderedDegree_strictMono,`SheafMixedKernelClosure.DegreeMono),
 (`JinWishart.mixedOrderedDegree_selection,`SheafMixedKernelClosure.DegreeSelection),
 (`JinWishart.mixedOrderedMinorProduct_pos,`SheafMixedKernelClosure.OrderedMinor),
 (`JinWishart.strictMono_fin_nat_index_le,`SheafMixedKernelClosure.IndexLe),
 (`JinWishart.mixedSelection_sorted_prefix,`SheafMixedKernelClosure.Prefix),
 (`JinWishart.mixedSelection_sorted_tail_ge,`SheafMixedKernelClosure.Tail),
 (`JinWishart.mixedSelection_sorted,`SheafMixedKernelClosure.Sorted),
 (`JinWishart.mixedSelectionMinorProduct_pos,`SheafMixedKernelClosure.MinorPos),
 (`JinWishart.mixedSelectionMinorProduct_nonneg,`SheafMixedKernelClosure.MinorNonneg),
 (`JinWishart.mixedLowestMinor_pos,`SheafMixedKernelClosure.LowestPos),
 (`JinWishart.finiteMixedKernel_det_lower_bound,`SheafMixedKernelClosure.FiniteFloor),
 (`JinWishart.finiteMixedKernel_det_pos,`SheafMixedKernelClosure.FinitePos),
 (`JinWishart.finiteMixedKernel_tendsto,`SheafMixedKernelClosure.Limit),
 (`JinWishart.infiniteMixedKernel_det_lower_bound,`SheafMixedKernelClosure.InfiniteFloor),
 (`JinWishart.infiniteMixedKernel_det_pos,`SheafMixedKernelClosure.InfinitePos)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mixed kernel literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
