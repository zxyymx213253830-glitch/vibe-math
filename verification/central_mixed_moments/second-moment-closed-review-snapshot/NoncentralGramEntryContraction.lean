import JinWishartFormalization.NoncentralLogDetCurvatureCoefficient
import JinWishartFormalization.ComplexGaussianShiftedFourthMoment

/-! The four-entry contraction needed for the closed noncentral trace-square.
Codex polynomial algebra. [需人工审查] Actual moment interpretation inherited.
-/
open Matrix
namespace JinWishart
noncomputable section

theorem noncentralGram_entry_fourth_contraction {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i j : Fin n) (k l : Fin m) :
    complexGaussianPolynomialMoment
      (((MvPolynomial.X (Sum.inr (k,i))+MvPolynomial.C (star (M k i))) *
        (MvPolynomial.X (Sum.inl (k,j))+MvPolynomial.C (M k j))) *
       ((MvPolynomial.X (Sum.inr (l,j))+MvPolynomial.C (star (M l j))) *
        (MvPolynomial.X (Sum.inl (l,i))+MvPolynomial.C (M l i))) : ComplexMatrixPolynomial m n) =
      star (M k i)*M k j*star (M l j)*M l i +
      (if i=j then 1 else 0)*(M l i*star (M l i)+M k i*star (M k i)) +
      (if k=l then 1 else 0)*(M k j*star (M k j)+M k i*star (M k i)) +
      (if i=j then 1 else 0)+(if k=l then 1 else 0) := by
  classical
  have he : (((MvPolynomial.X (Sum.inr (k,i))+MvPolynomial.C (star (M k i))) *
        (MvPolynomial.X (Sum.inl (k,j))+MvPolynomial.C (M k j))) *
       ((MvPolynomial.X (Sum.inr (l,j))+MvPolynomial.C (star (M l j))) *
        (MvPolynomial.X (Sum.inl (l,i))+MvPolynomial.C (M l i))) : ComplexMatrixPolynomial m n) =
      (MvPolynomial.X (Sum.inl (k,j))+MvPolynomial.C (M k j))*
      (MvPolynomial.X (Sum.inl (l,i))+MvPolynomial.C (M l i))*
      (MvPolynomial.X (Sum.inr (k,i))+MvPolynomial.C (star (M k i)))*
      (MvPolynomial.X (Sum.inr (l,j))+MvPolynomial.C (star (M l j))) := by ring
  rw [he,complexGaussianPolynomialMoment_shifted_fourth]
  simp only [Prod.mk.injEq,true_and,and_true]
  by_cases hij : i=j <;> by_cases hkl : k=l
  · subst j; subst l; simp; ring
  · subst j; simp [hkl,Ne.symm hkl]; ring
  · subst l; simp [hij,Ne.symm hij]; ring
  · simp [hij,hkl,Ne.symm hij,Ne.symm hkl]; ring

end
end JinWishart
#print axioms JinWishart.noncentralGram_entry_fourth_contraction
