import JinWishartFormalization.SubsetCauchyBinet
import JinWishartFormalization.GramMinorCoefficientBound

/-! The coefficient of det(I+t X^H X) is the full sum of squared q-minors.
Each row/column subset is included once. Codex finite algebra, all finite shapes. -/
open Matrix Polynomial Finset Function
namespace JinWishart
noncomputable section

theorem gram_principal_minor_eq_enumerated_gram {m n q : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (T : {T : Finset (Fin n) // T.card = q}) :
    ((complexGram X).submatrix (Subtype.val : T.val → Fin n) Subtype.val).det =
      (complexGram (X.submatrix id (fun j => (cardinalSubsetEnumeration T j).val))).det := by
  classical
  rw [← Matrix.det_submatrix_equiv_self (cardinalSubsetEnumeration T)]
  rfl

theorem gram_polynomial_coefficient_eq_sum_squared_minors {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (q : ℕ) :
    (((1+(Polynomial.X : ℂ[X]) • (complexGram X).map Polynomial.C).det).coeff q) =
      ∑ T : {T : Finset (Fin n) // T.card = q},
        ∑ S : {S : Finset (Fin m) // S.card = q},
          star ((X.submatrix (fun i => (cardinalSubsetEnumeration S i).val)
            (fun j => (cardinalSubsetEnumeration T j).val)).det) *
          (X.submatrix (fun i => (cardinalSubsetEnumeration S i).val)
            (fun j => (cardinalSubsetEnumeration T j).val)).det := by
  classical
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  rw [Finset.sum_subtype (p := fun T : Finset (Fin n) => T.card = q)
    (univ.powersetCard q) (by simp [Finset.mem_powersetCard])]
  apply Finset.sum_congr rfl
  intro T hT
  rw [gram_principal_minor_eq_enumerated_gram,gram_det_sum_squared_cardinal_minors]
  rfl

theorem gram_polynomial_coefficient_re_eq_sum_normSq_minors {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (q : ℕ) :
    ((((1+(Polynomial.X : ℂ[X]) • (complexGram X).map Polynomial.C).det).coeff q)).re =
      ∑ T : {T : Finset (Fin n) // T.card = q},
        ∑ S : {S : Finset (Fin m) // S.card = q},
          Complex.normSq ((X.submatrix (fun i => (cardinalSubsetEnumeration S i).val)
            (fun j => (cardinalSubsetEnumeration T j).val)).det) := by
  classical
  have h := congrArg Complex.re (gram_polynomial_coefficient_eq_sum_squared_minors X q)
  simpa [Complex.mul_re,Complex.star_def,Complex.normSq_apply] using h

end
end JinWishart
#print axioms JinWishart.gram_principal_minor_eq_enumerated_gram
#print axioms JinWishart.gram_polynomial_coefficient_eq_sum_squared_minors
#print axioms JinWishart.gram_polynomial_coefficient_re_eq_sum_normSq_minors
