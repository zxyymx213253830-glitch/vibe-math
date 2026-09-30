import Mathlib.Order.Interval.Finset.Fin

/-!
# Cardinalities of spectral index prefixes and tails
-/

namespace JinWishart

theorem finrankIndex_head_card {n : ℕ} (i : Fin n) :
    Fintype.card {j : Fin n // ¬ i < j} = i.val + 1 := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun j : Fin n => ¬ i < j) = Finset.Iic i := by
    ext j
    simp [not_lt]
  rw [hset, Fin.card_Iic]

theorem finrankIndex_tail_card {n : ℕ} (i : Fin n) :
    Fintype.card {j : Fin n // i ≤ j} = n - i.val := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun j : Fin n => i ≤ j) = Finset.Ici i := by
    ext j
    simp
  rw [hset, Fin.card_Ici]

end JinWishart
