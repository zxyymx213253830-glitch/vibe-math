import JinWishartFormalization.ComplexGaussianWickMoments

/-! Shifted complex fourth coordinate moment from the checked factorial Wick rule.
Codex deterministic polynomial expansion; constants need not be conjugate pairs.
[需人工审查] Application of the finite functional to actual Gaussian coordinates.
-/
namespace JinWishart
noncomputable section

theorem complexGaussianPolynomialMoment_shifted_fourth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι) (α β γ δ : ℂ) :
    complexGaussianPolynomialMoment
      ((MvPolynomial.X (Sum.inl a)+MvPolynomial.C α)*
       (MvPolynomial.X (Sum.inl b)+MvPolynomial.C β)*
       (MvPolynomial.X (Sum.inr c)+MvPolynomial.C γ)*
       (MvPolynomial.X (Sum.inr d)+MvPolynomial.C δ) : MvPolynomial (ι ⊕ ι) ℂ) =
      α*β*γ*δ + (if a=c then 1 else 0)*β*δ + (if a=d then 1 else 0)*β*γ +
      (if b=c then 1 else 0)*α*δ + (if b=d then 1 else 0)*α*γ +
      (if a=c ∧ b=d then 1 else 0)+(if a=d ∧ b=c then 1 else 0) := by
  classical
  let U : MvPolynomial (ι ⊕ ι) ℂ := MvPolynomial.X (Sum.inl a)
  let V : MvPolynomial (ι ⊕ ι) ℂ := MvPolynomial.X (Sum.inl b)
  let W : MvPolynomial (ι ⊕ ι) ℂ := MvPolynomial.X (Sum.inr c)
  let Y : MvPolynomial (ι ⊕ ι) ℂ := MvPolynomial.X (Sum.inr d)
  have he : (U+MvPolynomial.C α)*(V+MvPolynomial.C β)*(W+MvPolynomial.C γ)*(Y+MvPolynomial.C δ) =
      U*V*W*Y + δ • (U*V*W) + γ • (U*V*Y) + β • (U*W*Y) + α • (V*W*Y) +
      (γ*δ) • (U*V) + (β*δ) • (U*W) + (β*γ) • (U*Y) +
      (α*δ) • (V*W) + (α*γ) • (V*Y) + (α*β) • (W*Y) +
      (β*γ*δ) • U + (α*γ*δ) • V + (α*β*δ) • W + (α*β*γ) • Y + MvPolynomial.C (α*β*γ*δ) := by
    simp only [MvPolynomial.smul_eq_C_mul,map_mul]
    ring
  have hL (P : MvPolynomial (ι ⊕ ι) ℂ) :
      complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl
  change complexGaussianMomentLinear
    ((U+MvPolynomial.C α)*(V+MvPolynomial.C β)*(W+MvPolynomial.C γ)*(Y+MvPolynomial.C δ)) = _
  rw [he]
  simp only [map_add,map_smul]
  simp only [hL]
  simp only [U,V,W,Y,complexGaussianPolynomialMoment_fourth,
    complexGaussianPolynomialMoment_direct_direct_conjugate,
    complexGaussianPolynomialMoment_direct_conjugate_conjugate,
    complexGaussianPolynomialMoment_direct_pair,complexGaussianPolynomialMoment_conjugate_pair,
    complexGaussianPolynomialMoment_X_conj_X,complexGaussianPolynomialMoment_X,
    complexGaussianPolynomialMoment_C,smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add]
  ring

end
end JinWishart
#print axioms JinWishart.complexGaussianPolynomialMoment_shifted_fourth
