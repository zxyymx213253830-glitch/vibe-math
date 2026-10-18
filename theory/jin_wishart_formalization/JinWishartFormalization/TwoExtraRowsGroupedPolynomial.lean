import JinWishartFormalization.RectangularWishartTwoExtraRows
import JinWishartFormalization.FiniteSubsetPairGrouping

/-! Polynomial-time cardinality form of the actual two-extra-row minimum CDF.
Codex proof bodies. No new probability premise or spectral-density assumption.
[需人工审查] Interpretation inherited from the actual-law theorem.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def centralMixedMinorMomentByCards (t a b c p q : ℕ) : ℝ :=
  centralDeterminantPowerMoment (t-c) c (p+q) *
    (centralDeterminantPowerMoment (t-a) (a-c) p *
      centralDeterminantPowerMoment (t-b) (b-c) q)

theorem centralMixedMinorMoment_eq_byCards (t : ℕ) {n : ℕ}
    (S T : Finset (Fin n)) (p q : ℕ) :
    centralMixedMinorMoment t S T p q =
      centralMixedMinorMomentByCards t S.card T.card (S ∩ T).card p q := by
  have hs := finiteMinorOverlap_left_card S T
  have ht := finiteMinorOverlap_right_card S T
  have h0 : (S \ T).card = S.card-(S ∩ T).card := by omega
  have h1 : (T \ S).card = T.card-(S ∩ T).card := by omega
  unfold centralMixedMinorMoment centralMixedMinorMomentByCards
  rw [show t-(S ∩ T).card-(S \ T).card=t-S.card by omega,
    show t-(S ∩ T).card-(T \ S).card=t-T.card by omega,h0,h1]

def twoExtraRowGroupedPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  (((Nat.factorial n : ℕ) : ℝ) * ((Nat.factorial (n+1) : ℕ) : ℝ))⁻¹ *
    ∑ a ∈ Finset.range (n+1), ∑ c ∈ Finset.range (a+1),
      ∑ b ∈ Finset.range (n-a+1),
        (n.choose a : ℝ) * (a.choose c : ℝ) * ((n-a).choose b : ℝ) *
          (x^(n-a+(n-(c+b))) * centralMixedMinorMomentByCards n a (c+b) c 1 1)

theorem twoExtraRowMinimumPolynomial_eq_grouped (n : ℕ) (x : ℝ) :
    twoExtraRowMinimumPolynomial n x = twoExtraRowGroupedPolynomial n x := by
  unfold twoExtraRowMinimumPolynomial twoExtraRowGroupedPolynomial
  congr 1
  simp_rw [centralMixedMinorMoment_eq_byCards]
  exact sum_finsets_pair_cardinalities n
    (fun a b c => x^(n-a+(n-b)) * centralMixedMinorMomentByCards n a b c 1 1)

theorem actualTwoExtraRows_minimum_CDF_grouped (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := n+2) (n := n)))
      {z | centralGaussianSampleMinimum (n+2) n hn z ≤ x}).toReal =
      1-Real.exp (-(n : ℝ)*x) * twoExtraRowGroupedPolynomial n x := by
  rw [actualTwoExtraRows_minimum_CDF n hn x hx,twoExtraRowMinimumPolynomial_eq_grouped]

theorem actualTwoExtraRows_covariance_minimum_CDF_grouped (n : ℕ) (hn : 0 < n)
    (v : ℝ) (hv : 0 < v) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := n+2) (n := n)))
      {z | centralGaussianSampleMinimum (n+2) n hn (Real.sqrt v • z) ≤ x}).toReal =
      1-Real.exp (-(n : ℝ)*(x/v)) * twoExtraRowGroupedPolynomial n (x/v) := by
  rw [actualTwoExtraRows_covariance_minimum_CDF n hn v hv x hx,
    twoExtraRowMinimumPolynomial_eq_grouped]

end
end JinWishart
#print axioms JinWishart.centralMixedMinorMoment_eq_byCards
#print axioms JinWishart.twoExtraRowMinimumPolynomial_eq_grouped
#print axioms JinWishart.actualTwoExtraRows_minimum_CDF_grouped
#print axioms JinWishart.actualTwoExtraRows_covariance_minimum_CDF_grouped
