import JinWishartFormalization.GramMinimumLeftComparison
import Mathlib.Order.Interval.Finset.Fin

/-! The positive entries of a descending finite real sequence form a prefix.
Codex finite proofs; negative entries allowed, no probabilistic assumptions. -/
namespace JinWishart
noncomputable section

theorem antitone_positive_iff_lt_count {n : ℕ} (f : Fin n → ℝ)
    (hf : Antitone f) (i : Fin n) :
    0<f i ↔ i.val<(Finset.univ.filter (fun j => 0<f j)).card := by
  classical
  let s := Finset.univ.filter (fun j => 0<f j)
  change 0<f i ↔ i.val<s.card
  constructor
  · intro hi
    have hs : Finset.Iic i ⊆ s := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.trans_le (hf (Finset.mem_Iic.mp hj))⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    omega
  · intro hi
    by_contra hp
    have hs : s ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      have hij : i≤j := le_of_not_gt hji
      exact hp ((Finset.mem_filter.mp hj).2.trans_le (hf hij))
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    omega

theorem antitone_min_positive_at_count {n : ℕ} (f : Fin n → ℝ)
    (hf : Antitone f) (i : Fin n)
    (hc : (Finset.univ.filter (fun j => 0<f j)).card=i.val+1) :
    0<f i ∧ ∀ j,0<f j → f i≤f j := by
  have hi : 0<f i := (antitone_positive_iff_lt_count f hf i).mpr (by rw [hc];omega)
  refine ⟨hi,?_⟩
  intro j hj
  have hjc := (antitone_positive_iff_lt_count f hf j).mp hj
  rw [hc] at hjc
  apply hf
  change j.val ≤ i.val
  omega

end
end JinWishart
#print axioms JinWishart.antitone_positive_iff_lt_count
#print axioms JinWishart.antitone_min_positive_at_count
