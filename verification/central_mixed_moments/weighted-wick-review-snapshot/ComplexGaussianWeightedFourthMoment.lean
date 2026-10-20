import JinWishartFormalization.ComplexGaussianWickMoments

/-! Centered weighted complex Wick contraction, finite coordinate types may be empty.
Codex algebra. Coefficients of conjugate variables are already conjugated;
no extra star is applied. [需人工审查] Actual Gaussian integral interpretation.
-/
namespace JinWishart
noncomputable section

def complexDirectLinearPolynomial {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    MvPolynomial (ι ⊕ ι) ℂ := ∑ i, MvPolynomial.C (a i)*MvPolynomial.X (Sum.inl i)

def complexConjugateLinearPolynomial {ι : Type*} [Fintype ι] (c : ι → ℂ) :
    MvPolynomial (ι ⊕ ι) ℂ := ∑ i, MvPolynomial.C (c i)*MvPolynomial.X (Sum.inr i)

theorem complexGaussianPolynomialMoment_weighted_fourth {ι : Type*} [Fintype ι]
    (a b c d : ι → ℂ) :
    complexGaussianPolynomialMoment
      (complexDirectLinearPolynomial a*complexDirectLinearPolynomial b*
        complexConjugateLinearPolynomial c*complexConjugateLinearPolynomial d) =
      (∑ i, a i*c i)*(∑ j, b j*d j)+(∑ i, a i*d i)*(∑ j, b j*c j) := by
  classical
  have he : complexDirectLinearPolynomial a*complexDirectLinearPolynomial b*
      complexConjugateLinearPolynomial c*complexConjugateLinearPolynomial d =
      ∑ l, ∑ k, ∑ j, ∑ i, (a i*b j*c k*d l) •
        (MvPolynomial.X (Sum.inl i)*MvPolynomial.X (Sum.inl j)*
          MvPolynomial.X (Sum.inr k)*MvPolynomial.X (Sum.inr l)) := by
    simp only [complexDirectLinearPolynomial,complexConjugateLinearPolynomial,
      Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    simp only [MvPolynomial.smul_eq_C_mul,map_mul]
    ring
  have hL (P : MvPolynomial (ι ⊕ ι) ℂ) :
      complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl
  change complexGaussianMomentLinear _ = _
  rw [he]
  simp only [map_sum,map_smul]
  simp only [hL,complexGaussianPolynomialMoment_fourth,smul_eq_mul]
  simp only [mul_add,mul_ite,mul_one,mul_zero,ite_and,Finset.sum_add_distrib,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const_zero]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  have hi1 (x : ι) : (∑ y, a y*b x*c y) = (∑ y, a y*c y)*b x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hi2 (x : ι) : (∑ y, a x*b y*c y) = a x*(∑ y, b y*c y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [hi1,hi2,mul_assoc]
  have hi3 (x : ι) : a x*((∑ y, b y*c y)*d x) = (∑ y, b y*c y)*(a x*d x) := by ring
  simp_rw [hi3]
  simp only [← Finset.mul_sum]
  ring

end
end JinWishart
#print axioms JinWishart.complexGaussianPolynomialMoment_weighted_fourth
