import JinWishartFormalization.RectangularDeterminantExpansion
import JinWishartFormalization.WishartProbability
import Mathlib.Data.Fintype.Perm

/-! Permutation-averaged Cauchy--Binet, retaining all index functions.
The factorial multiplicity is explicit; no subset enumeration is assumed.
Codex deterministic algebra, including empty shapes. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

theorem rectangular_det_permutation_weight_sum {q m : ℕ}
    (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ)
    (σ : Equiv.Perm (Fin q)) :
    (∑ f : Fin q → Fin m, (∏ i, A (σ i) (f i))*(B.submatrix f id).det) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ)*(A*B).det := by
  classical
  let E : (Fin q → Fin m) ≃ (Fin q → Fin m) :=
    { toFun := fun f i => f (σ i)
      invFun := fun f i => f (σ.symm i)
      left_inv := by intro f; funext i; simp
      right_inv := by intro f; funext i; simp }
  calc
    _ = ∑ g : Fin q → Fin m, (∏ i, A (σ i) (E g i))*(B.submatrix (E g) id).det :=
      (E.sum_comp (fun f => (∏ i, A (σ i) (f i))*(B.submatrix f id).det)).symm
    _ = ∑ g : Fin q → Fin m, ((Equiv.Perm.sign σ : ℤ) : ℂ)*
        ((∏ i, A i (g i))*(B.submatrix g id).det) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hp : (∏ i, A (σ i) (E g i)) = ∏ i, A i (g i) :=
        Equiv.prod_comp σ (fun i => A i (g i))
      have he : B.submatrix (E g) id = (B.submatrix g id).submatrix σ id := by
        ext i j
        rfl
      rw [hp,he,Matrix.det_permute]
      ring
    _ = _ := by rw [← Finset.mul_sum,← det_mul_rectangular_sum_functions]

theorem det_mul_rectangular_factorial_sum_functions {q m : ℕ}
    (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ) :
    (q.factorial : ℂ)*(A*B).det =
      ∑ f : Fin q → Fin m, (A.submatrix id f).det*(B.submatrix f id).det := by
  classical
  have ha (f : Fin q → Fin m) : (A.submatrix id f).det =
      ∑ σ : Equiv.Perm (Fin q), ((Equiv.Perm.sign σ : ℤ) : ℂ)*(∏ i, A (σ i) (f i)) := by
    rw [Matrix.det_apply']
    rfl
  symm
  calc
    _ = ∑ σ : Equiv.Perm (Fin q), ((Equiv.Perm.sign σ : ℤ) : ℂ)*
        (∑ f : Fin q → Fin m, (∏ i, A (σ i) (f i))*(B.submatrix f id).det) := by
      simp_rw [ha,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      ring
    _ = ∑ _σ : Equiv.Perm (Fin q), (A*B).det := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [rectangular_det_permutation_weight_sum]
      have hs : (((Equiv.Perm.sign σ : ℤ) : ℂ))*(((Equiv.Perm.sign σ : ℤ) : ℂ))=1 := by
        exact_mod_cast Int.isUnit_mul_self (Equiv.Perm.sign σ).isUnit
      rw [← mul_assoc,hs,one_mul]
    _ = _ := by simp [Fintype.card_perm]

theorem gram_det_factorial_sum_squared_minors {m q : ℕ}
    (B : Matrix (Fin m) (Fin q) ℂ) :
    (q.factorial : ℂ)*(complexGram B).det =
      ∑ f : Fin q → Fin m, star ((B.submatrix f id).det)*(B.submatrix f id).det := by
  classical
  have h := det_mul_rectangular_factorial_sum_functions B.conjTranspose B
  have he (f : Fin q → Fin m) : B.conjTranspose.submatrix id f = (B.submatrix f id).conjTranspose := by
    ext i j
    rfl
  simpa only [he,Matrix.det_conjTranspose,complexGram] using h

theorem squared_minor_le_factorial_gram_det {m q : ℕ}
    (B : Matrix (Fin m) (Fin q) ℂ) (f : Fin q → Fin m) :
    Complex.normSq ((B.submatrix f id).det) ≤ (q.factorial : ℝ)*(complexGram B).det.re := by
  classical
  have h := congrArg Complex.re (gram_det_factorial_sum_squared_minors B)
  have ht (z : ℂ) : (star z*z).re = Complex.normSq z := by
    simp [Complex.mul_re,Complex.normSq_apply,Complex.star_def]
  have hr : (q.factorial : ℝ)*(complexGram B).det.re =
      ∑ g : Fin q → Fin m, Complex.normSq ((B.submatrix g id).det) := by
    simpa [Complex.mul_re,Complex.normSq_apply] using h
  rw [hr]
  exact Finset.single_le_sum (fun g _ => Complex.normSq_nonneg ((B.submatrix g id).det))
    (Finset.mem_univ f)

end
end JinWishart
#print axioms JinWishart.rectangular_det_permutation_weight_sum
#print axioms JinWishart.det_mul_rectangular_factorial_sum_functions
#print axioms JinWishart.gram_det_factorial_sum_squared_minors
#print axioms JinWishart.squared_minor_le_factorial_gram_det
