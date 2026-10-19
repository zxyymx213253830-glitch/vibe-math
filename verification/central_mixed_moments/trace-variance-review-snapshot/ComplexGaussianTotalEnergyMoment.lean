import JinWishartFormalization.ComplexGaussianShiftedFourthMoment

/-! Exact second moment of the total shifted complex Gaussian energy.
Codex algebra for the existing actual factorial functional. Different from
trace of a Gram square. [需人工审查] Actual moment transport interpretation.
-/
namespace JinWishart
noncomputable section

def complexTotalEnergyPolynomial {ι : Type*} [Fintype ι] (μ : ι → ℂ) :
    MvPolynomial (ι ⊕ ι) ℂ :=
  ∑ a, (MvPolynomial.X (Sum.inl a)+MvPolynomial.C (μ a))*
    (MvPolynomial.X (Sum.inr a)+MvPolynomial.C (star (μ a)))

theorem complexGaussianPolynomialMoment_shifted_energy_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℂ) (a b : ι) :
    complexGaussianPolynomialMoment
      (((MvPolynomial.X (Sum.inl a)+MvPolynomial.C (μ a))*
        (MvPolynomial.X (Sum.inr a)+MvPolynomial.C (star (μ a)))) *
       ((MvPolynomial.X (Sum.inl b)+MvPolynomial.C (μ b))*
        (MvPolynomial.X (Sum.inr b)+MvPolynomial.C (star (μ b)))) : MvPolynomial (ι ⊕ ι) ℂ) =
      (1+μ a*star (μ a))*(1+μ b*star (μ b)) +
        (if a=b then 1 else 0)*(1+2*μ a*star (μ a)) := by
  classical
  have he : (((MvPolynomial.X (Sum.inl a)+MvPolynomial.C (μ a))*
        (MvPolynomial.X (Sum.inr a)+MvPolynomial.C (star (μ a)))) *
       ((MvPolynomial.X (Sum.inl b)+MvPolynomial.C (μ b))*
        (MvPolynomial.X (Sum.inr b)+MvPolynomial.C (star (μ b)))) : MvPolynomial (ι ⊕ ι) ℂ) =
      (MvPolynomial.X (Sum.inl a)+MvPolynomial.C (μ a))*
      (MvPolynomial.X (Sum.inl b)+MvPolynomial.C (μ b))*
      (MvPolynomial.X (Sum.inr a)+MvPolynomial.C (star (μ a)))*
      (MvPolynomial.X (Sum.inr b)+MvPolynomial.C (star (μ b))) := by ring
  rw [he,complexGaussianPolynomialMoment_shifted_fourth]
  by_cases hab : a=b
  · subst b; simp; ring
  · simp [hab,Ne.symm hab]; ring

theorem complexGaussianPolynomialMoment_total_energy_sq {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) :
    complexGaussianPolynomialMoment (complexTotalEnergyPolynomial μ ^ 2) =
      ((Fintype.card ι : ℂ)+∑ a, μ a*star (μ a))^2 +
        (Fintype.card ι : ℂ)+2*(∑ a, μ a*star (μ a)) := by
  classical
  have hL (P : MvPolynomial (ι ⊕ ι) ℂ) :
      complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl
  change complexGaussianMomentLinear (complexTotalEnergyPolynomial μ ^ 2) = _
  simp only [complexTotalEnergyPolynomial,pow_two,Finset.sum_mul,Finset.mul_sum,map_sum]
  simp only [hL,complexGaussianPolynomialMoment_shifted_energy_pair]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have htwo : (∑ a, 2*μ a*(starRingEnd ℂ) (μ a)) =
      2*(∑ a, μ a*(starRingEnd ℂ) (μ a)) := by
    simp only [mul_assoc,Finset.mul_sum]
  linear_combination htwo

end
end JinWishart
#print axioms JinWishart.complexGaussianPolynomialMoment_shifted_energy_pair
#print axioms JinWishart.complexGaussianPolynomialMoment_total_energy_sq
