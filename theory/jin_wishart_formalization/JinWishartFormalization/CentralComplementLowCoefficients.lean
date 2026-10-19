import JinWishartFormalization.CentralComplementMinorPolynomial
import JinWishartFormalization.FiniteChooseTruncation
import Mathlib.Data.Nat.Choose.Cast

/-! Bounded computation of low coefficients after the actual complement reindex.
Codex deterministic algebra. Not an assumed density or finite-sample proof. -/
namespace JinWishart
noncomputable section

def complementCoefficientTerm (r h t k : ℕ) : ℝ :=
  if r+(h+t)=k then
    1/(((r+t+1 : ℕ) : ℝ)*(r.factorial : ℝ)*((h+t).factorial : ℝ))
  else 0

theorem centralComplementMinorPolynomial_coeff_grouped (N k : ℕ) :
    (centralComplementMinorPolynomial N).coeff k =
      ∑ r ∈ Finset.range (N+1), (N.choose r : ℝ)*
        ∑ h ∈ Finset.range (r+1), (r.choose h : ℝ)*
          ∑ t ∈ Finset.range (N-r+1), ((N-r).choose t : ℝ)*complementCoefficientTerm r h t k := by
  classical
  have hU (R T : Finset (Fin N)) : (R∪T).card=R.card+T.card-(R∩T).card := by
    have h := Finset.card_union_add_card_inter R T
    omega
  simp only [centralComplementMinorPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  simp_rw [hU]
  rw [sum_finsets_pair_cardinalities N (fun r s h =>
    if r+s=k then 1/(((r+s-h+1 : ℕ) : ℝ)*(r.factorial : ℝ)*(s.factorial : ℝ)) else 0)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro t _
  unfold complementCoefficientTerm
  rw [show r+(h+t)-h=r+t by omega]
  ring

theorem centralComplementMinorPolynomial_coeff_bounded (N k : ℕ) :
    (centralComplementMinorPolynomial N).coeff k =
      ∑ r ∈ Finset.range (k+1), (N.choose r : ℝ)*
        ∑ h ∈ Finset.range (r+1), (r.choose h : ℝ)*
          ∑ t ∈ Finset.range (k+1), ((N-r).choose t : ℝ)*complementCoefficientTerm r h t k := by
  rw [centralComplementMinorPolynomial_coeff_grouped]
  rw [sum_range_choose_truncate N (k+1) _ (by
    intro r hr
    apply Finset.sum_eq_zero
    intro h _
    have hzero : (∑ t ∈ Finset.range (N-r+1),
        ((N-r).choose t : ℝ)*complementCoefficientTerm r h t k)=0 := by
      apply Finset.sum_eq_zero
      intro t _
      simp only [complementCoefficientTerm,ite_eq_right (show r+(h+t)≠k by omega),mul_zero]
    rw [hzero,mul_zero])]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  exact sum_range_choose_truncate (N-r) (k+1) _ (by
    intro t ht
    simp only [complementCoefficientTerm,ite_eq_right (show r+(h+t)≠k by omega)])

end
end JinWishart
#print axioms JinWishart.centralComplementMinorPolynomial_coeff_grouped
#print axioms JinWishart.centralComplementMinorPolynomial_coeff_bounded
