import JinWishartFormalization.TwoExtraRowsGroupedPolynomial

/-!
# Factorial products needed by the two-surplus sharp coefficient

Codex deterministic algebra. Uses the existing proved first-moment product.
No new density or probability assumption. [需人工审查] Inherited model interpretation.
-/
namespace JinWishart
noncomputable section

theorem centralDeterminantPowerMoment_one_factorial (d n : ℕ) :
    centralDeterminantPowerMoment d n 1 =
      ((d+n).factorial : ℝ)/(d.factorial : ℝ) := factorial_ratio_product d n

theorem centralDeterminantPowerMoment_two_factorial (d n : ℕ) :
    centralDeterminantPowerMoment d n 2 =
      (((d+n).factorial : ℝ)*((d+n+1).factorial : ℝ))/
        ((d.factorial : ℝ)*((d+1).factorial : ℝ)) := by
  rw [show (2 : ℕ)=1+1 by omega,centralDeterminantPowerMoment_add,
    centralDeterminantPowerMoment_one_factorial,centralDeterminantPowerMoment_one_factorial]
  rw [show d+1+n=d+n+1 by omega]
  ring

theorem centralMixedMinorMomentByCards_normalized (N a b c : ℕ)
    (ha : a≤N) (hb : b≤N) (hca : c≤a) (hcb : c≤b) :
    centralMixedMinorMomentByCards N a b c 1 1/
      ((N.factorial : ℝ)*((N+1).factorial : ℝ)) =
      1/(((N-c+1 : ℕ) : ℝ)*((N-a).factorial : ℝ)*((N-b).factorial : ℝ)) := by
  have hcN : c≤N := hca.trans ha
  have hA : N-a+(a-c)=N-c := by omega
  have hB : N-b+(b-c)=N-c := by omega
  unfold centralMixedMinorMomentByCards
  rw [show (1+1 : ℕ)=2 by omega,centralDeterminantPowerMoment_two_factorial,
    centralDeterminantPowerMoment_one_factorial,centralDeterminantPowerMoment_one_factorial,
    Nat.sub_add_cancel hcN,hA,hB,Nat.factorial_succ]
  have h0 : (N.factorial : ℝ)≠0 := by positivity
  have h1 : ((N+1).factorial : ℝ)≠0 := by positivity
  have hc : ((N-c).factorial : ℝ)≠0 := by positivity
  have ha0 : ((N-a).factorial : ℝ)≠0 := by positivity
  have hb0 : ((N-b).factorial : ℝ)≠0 := by positivity
  have hc1 : ((N-c+1 : ℕ) : ℝ)≠0 := by positivity
  push_cast
  field_simp
  rw [Nat.factorial_succ]
  push_cast
  ring

end
end JinWishart
#print axioms JinWishart.centralDeterminantPowerMoment_one_factorial
#print axioms JinWishart.centralDeterminantPowerMoment_two_factorial
#print axioms JinWishart.centralMixedMinorMomentByCards_normalized
