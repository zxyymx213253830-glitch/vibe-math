import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Binomial sums with a bounded coefficient support.
Codex deterministic proofs after exact sparse/binomial controls. -/
namespace JinWishart
noncomputable section

theorem sum_range_choose_truncate (N K : ℕ) (f : ℕ → ℝ)
    (hz : ∀ i, K ≤ i → f i=0) :
    (∑ i ∈ Finset.range (N+1), (N.choose i : ℝ)*f i) =
      ∑ i ∈ Finset.range K, (N.choose i : ℝ)*f i := by
  by_cases hK : K≤N+1
  · symm
    apply Finset.sum_subset (Finset.range_mono hK)
    intro i hi hnot
    have hKi : K ≤ i := by simpa only [Finset.mem_range,not_lt] using hnot
    rw [hz i hKi,mul_zero]
  · apply Finset.sum_subset (Finset.range_mono (le_of_not_ge hK))
    intro i hi hnot
    have hNi : N < i := by simp only [Finset.mem_range] at hnot; omega
    rw [Nat.choose_eq_zero_of_lt hNi,Nat.cast_zero,zero_mul]

end
end JinWishart
#print axioms JinWishart.sum_range_choose_truncate
