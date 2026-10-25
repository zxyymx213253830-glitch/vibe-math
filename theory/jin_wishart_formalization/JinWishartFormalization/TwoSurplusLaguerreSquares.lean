import JinWishartFormalization.FiniteSupersetKernel
import JinWishartFormalization.TwoSurplusOverlapKernel
import JinWishartFormalization.RectangularWishartOneExtraRow

/-! Codex. Seed2026102504 exact averages and seed2505 signed square controls
precede source. An average-square form of the ALREADY PROVED actual polynomial.
Not yet equality with the original T1 determinant candidate.
[需人工审查] Inherited actual model/CDF and eventual original-paper mapping. -/
open Finset MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

private theorem sum_complements (n : ℕ) (g : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n),g S)=∑ S : Finset (Fin n),g Sᶜ := by
  let e : Finset (Fin n) ≃ Finset (Fin n) :=
    { toFun := fun S => Sᶜ
      invFun := fun S => Sᶜ
      left_inv := by intro S;simp
      right_inv := by intro S;simp }
  exact (Equiv.sum_comp e g).symm

private theorem subset_polynomial_sum (n : ℕ) (R : Finset (Fin n)) (x : ℝ) :
    (∑ U ∈ R.powerset,x^U.card/(U.card.factorial : ℝ))=
      oneExtraRowMinimumPolynomial R.card x := by
  rw [sum_powerset]
  simp_rw [sum_powersetCard _ R (fun k : ℕ => x^k/(k.factorial : ℝ))]
  simp only [nsmul_eq_mul]
  unfold oneExtraRowMinimumPolynomial
  apply sum_congr rfl
  intro k _
  ring

theorem twoExtraRowMinimumPolynomial_eq_meanSquares (n : ℕ) (x : ℝ) :
    twoExtraRowMinimumPolynomial n x =
      (∑ k ∈ range (n+1),(oneExtraRowMinimumPolynomial k x)^2)/((n+1 : ℕ) : ℝ) := by
  classical
  let O : Finset (Fin n) → Finset (Fin n) → ℝ := fun S T =>
    x^(n-S.card+(n-T.card))/
      (((n-(S ∩ T).card+1 : ℕ) : ℝ)*((n-S.card).factorial : ℝ)*((n-T.card).factorial : ℝ))
  let f : Finset (Fin n) → ℝ := fun U => x^U.card/(U.card.factorial : ℝ)
  have hterm (U V : Finset (Fin n)) : O Uᶜ Vᶜ =
      f U*f V/(((U ∪ V).card+1 : ℕ) : ℝ) := by
    have hU : U.card≤n := by simpa using card_le_card (subset_univ U)
    have hV : V.card≤n := by simpa using card_le_card (subset_univ V)
    have hUV : (U ∪ V).card≤n := by simpa using card_le_card (subset_univ (U ∪ V))
    dsimp only [O,f]
    rw [← compl_union]
    simp only [card_compl,Fintype.card_fin,Nat.sub_sub_self hU,Nat.sub_sub_self hV,Nat.sub_sub_self hUV,pow_add]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hp : twoExtraRowMinimumPolynomial n x=
      ∑ U : Finset (Fin n), ∑ V : Finset (Fin n), f U*f V/(((U ∪ V).card+1 : ℕ) : ℝ) := by
    calc
      _ = ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),O S T :=
        twoExtraRowMinimumPolynomial_eq_overlapKernel n x
      _ = ∑ U : Finset (Fin n), ∑ T : Finset (Fin n),O Uᶜ T :=
        sum_complements n _
      _ = ∑ U : Finset (Fin n), ∑ V : Finset (Fin n),O Uᶜ Vᶜ := by
        apply sum_congr rfl
        intro U _
        exact sum_complements n _
      _ = _ := by
        apply sum_congr rfl
        intro U _
        apply sum_congr rfl
        intro V _
        exact hterm U V
  rw [hp,finiteSubsetPairKernel_square_sum]
  have hs (R : Finset (Fin n)) : (∑ U ∈ R.powerset,f U)=oneExtraRowMinimumPolynomial R.card x :=
    subset_polynomial_sum n R x
  simp_rw [hs]
  rw [sum_finsets_card_fintype (α := Fin n) (fun k : ℕ =>
    (oneExtraRowMinimumPolynomial k x)^2/(((n+1 : ℕ) : ℝ)*(n.choose k : ℝ)))]
  simp only [Fintype.card_fin]
  rw [sum_div]
  apply sum_congr rfl
  intro k hk
  have hk0 : k≤n := Nat.le_of_lt_succ (mem_range.mp hk)
  have hc : (n.choose k : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hk0).ne'
  have hn : ((n+1 : ℕ) : ℝ)≠0 := by positivity
  field_simp

theorem actualTwoExtraRows_minimum_CDF_meanSquares (n : ℕ) (hn : 0<n) (x : ℝ) (hx : 0≤x) :
    ((stdGaussian (ComplexSample (m := n+2) (n := n)))
      {z | centralGaussianSampleMinimum (n+2) n hn z≤x}).toReal =
        1-Real.exp (-(n : ℝ)*x)*
          ((∑ k ∈ range (n+1),(oneExtraRowMinimumPolynomial k x)^2)/((n+1 : ℕ) : ℝ)) := by
  rw [actualTwoExtraRows_minimum_CDF n hn x hx,twoExtraRowMinimumPolynomial_eq_meanSquares]

end
end JinWishart
#print axioms JinWishart.twoExtraRowMinimumPolynomial_eq_meanSquares
#print axioms JinWishart.actualTwoExtraRows_minimum_CDF_meanSquares
