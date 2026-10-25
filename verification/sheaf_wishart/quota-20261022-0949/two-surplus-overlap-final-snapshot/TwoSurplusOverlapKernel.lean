import JinWishartFormalization.TwoExtraRowsGroupedPolynomial

/-! Codex. Seed2026102504 exact controls before source. Finite overlap-moment
and subset-kernel algebra only, not a new probability law.
[需人工审查] Existing actual mixed-minor model and later original-T1 mapping. -/
open Matrix
namespace JinWishart
noncomputable section

private theorem byCards_first_product_closed (n a b c : ℕ)
    (ha : a≤n) (hb : b≤n) (hca : c≤a) (hcb : c≤b) :
    centralMixedMinorMomentByCards n a b c 1 1 =
      ((n.factorial : ℝ)*((n+1).factorial : ℝ))/
        (((n-c+1 : ℕ) : ℝ)*((n-a).factorial : ℝ)*((n-b).factorial : ℝ)) := by
  have hc : c≤n := hca.trans ha
  unfold centralMixedMinorMomentByCards
  rw [centralDeterminantPowerMoment_add,centralDeterminantPowerMoment_one,
    centralDeterminantPowerMoment_one,centralDeterminantPowerMoment_one,centralDeterminantPowerMoment_one]
  rw [show n-c+c=n by omega,show n-c+1+c=n+1 by omega,
    show n-a+(a-c)=n-c by omega,show n-b+(b-c)=n-c by omega]
  rw [Nat.factorial_succ (n-c)]
  push_cast
  have h0 : ((n-c).factorial : ℝ)≠0 := by positivity
  have ha0 : ((n-a).factorial : ℝ)≠0 := by positivity
  have hb0 : ((n-b).factorial : ℝ)≠0 := by positivity
  have h1 : ((n-c : ℕ) : ℝ)+1≠0 := by positivity
  field_simp
  <;> ring

theorem centralMixedMinorMoment_first_product_closed (n : ℕ) (S T : Finset (Fin n)) :
    centralMixedMinorMoment n S T 1 1 =
      ((n.factorial : ℝ)*((n+1).factorial : ℝ))/
        (((n-(S ∩ T).card+1 : ℕ) : ℝ)*((n-S.card).factorial : ℝ)*((n-T.card).factorial : ℝ)) := by
  rw [centralMixedMinorMoment_eq_byCards]
  apply byCards_first_product_closed
  · simpa using Finset.card_le_card (Finset.subset_univ S)
  · simpa using Finset.card_le_card (Finset.subset_univ T)
  · exact Finset.card_le_card Finset.inter_subset_left
  · exact Finset.card_le_card Finset.inter_subset_right

theorem twoExtraRowMinimumPolynomial_eq_overlapKernel (n : ℕ) (x : ℝ) :
    twoExtraRowMinimumPolynomial n x =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        x^(n-S.card+(n-T.card))/
          (((n-(S ∩ T).card+1 : ℕ) : ℝ)*((n-S.card).factorial : ℝ)*((n-T.card).factorial : ℝ)) := by
  classical
  unfold twoExtraRowMinimumPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [centralMixedMinorMoment_first_product_closed]
  have h0 : (n.factorial : ℝ)≠0 := by positivity
  have h1 : ((n+1).factorial : ℝ)≠0 := by positivity
  field_simp

end
end JinWishart
#print axioms JinWishart.centralMixedMinorMoment_first_product_closed
#print axioms JinWishart.twoExtraRowMinimumPolynomial_eq_overlapKernel
