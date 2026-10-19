import JinWishartFormalization.CentralWishartMomentFactorials
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Two-surplus polynomial reindexed by missing principal subsets

Codex. Finite deterministic algebra, no new actual-density assumption.
[需人工审查] Inherited actual minimum-law interpretation.
-/
open Matrix
namespace JinWishart
noncomputable section

theorem normalized_complement_minor_moment (N : ℕ) (R T : Finset (Fin N)) :
    centralMixedMinorMomentByCards N Rᶜ.card Tᶜ.card (Rᶜ ∩ Tᶜ).card 1 1/
      ((N.factorial : ℝ)*((N+1).factorial : ℝ)) =
      1/((((R∪T).card+1 : ℕ) : ℝ)*(R.card.factorial : ℝ)*(T.card.factorial : ℝ)) := by
  have hR : R.card≤N := by simpa using R.card_le_univ
  have hT : T.card≤N := by simpa using T.card_le_univ
  have hU : (R∪T).card≤N := by simpa using (R∪T).card_le_univ
  have h := centralMixedMinorMomentByCards_normalized N Rᶜ.card Tᶜ.card (Rᶜ∩Tᶜ).card
    (by simpa using Rᶜ.card_le_univ) (by simpa using Tᶜ.card_le_univ)
    (Finset.card_le_card Finset.inter_subset_left) (Finset.card_le_card Finset.inter_subset_right)
  simpa only [← Finset.compl_union,Finset.card_compl,Fintype.card_fin,
    Nat.sub_sub_self hR,Nat.sub_sub_self hT,Nat.sub_sub_self hU] using h

def centralComplementMinorPolynomial (N : ℕ) : Polynomial ℝ :=
  ∑ R : Finset (Fin N), ∑ T : Finset (Fin N),
    Polynomial.monomial (R.card+T.card)
      (1/((((R∪T).card+1 : ℕ) : ℝ)*(R.card.factorial : ℝ)*(T.card.factorial : ℝ)))

theorem centralComplementMinorPolynomial_eval (N : ℕ) (x : ℝ) :
    (centralComplementMinorPolynomial N).eval x =
      ∑ R : Finset (Fin N), ∑ T : Finset (Fin N),
        x^(R.card+T.card)/
          ((((R∪T).card+1 : ℕ) : ℝ)*(R.card.factorial : ℝ)*(T.card.factorial : ℝ)) := by
  classical
  simp only [centralComplementMinorPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro R _
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem twoExtraRowMinimumPolynomial_eq_complement (N : ℕ) (x : ℝ) :
    twoExtraRowMinimumPolynomial N x=(centralComplementMinorPolynomial N).eval x := by
  classical
  let f : Finset (Fin N) → Finset (Fin N) → ℝ := fun S T =>
    x^(N-S.card+(N-T.card))*
      (centralMixedMinorMomentByCards N S.card T.card (S∩T).card 1 1/
        ((N.factorial : ℝ)*((N+1).factorial : ℝ)))
  have hn : twoExtraRowMinimumPolynomial N x=∑ S : Finset (Fin N), ∑ T : Finset (Fin N), f S T := by
    unfold twoExtraRowMinimumPolynomial
    simp_rw [centralMixedMinorMoment_eq_byCards]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    dsimp only [f]
    ring
  let e : Finset (Fin N) ≃ Finset (Fin N) :=
    { toFun := fun S => Sᶜ
      invFun := fun S => Sᶜ
      left_inv := fun S => compl_compl S
      right_inv := fun S => compl_compl S }
  have hre : (∑ R : Finset (Fin N), ∑ T : Finset (Fin N), f Rᶜ Tᶜ)=
      ∑ R : Finset (Fin N), ∑ T : Finset (Fin N), f R T := by
    calc
      _ = ∑ R : Finset (Fin N), ∑ T : Finset (Fin N), f Rᶜ T := by
        apply Finset.sum_congr rfl
        intro R _
        exact Equiv.sum_comp e (fun T => f Rᶜ T)
      _ = _ := Equiv.sum_comp e (fun R => ∑ T : Finset (Fin N), f R T)
  rw [hn,← hre,centralComplementMinorPolynomial_eval]
  apply Finset.sum_congr rfl
  intro R _
  apply Finset.sum_congr rfl
  intro T _
  dsimp only [f]
  rw [normalized_complement_minor_moment]
  have hR : R.card≤N := by simpa using R.card_le_univ
  have hT : T.card≤N := by simpa using T.card_le_univ
  simp only [Finset.card_compl,Fintype.card_fin,Nat.sub_sub_self hR,Nat.sub_sub_self hT]
  ring

end
end JinWishart
#print axioms JinWishart.normalized_complement_minor_moment
#print axioms JinWishart.centralComplementMinorPolynomial_eval
#print axioms JinWishart.twoExtraRowMinimumPolynomial_eq_complement
