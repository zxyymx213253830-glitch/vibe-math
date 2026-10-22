import JinWishartFormalization.FiniteSubsetFunctionSum

/-! Exact subset-grouped rectangular Cauchy--Binet over complex matrices.
One cardinality-q subset contributes once; no residual factorial.
Codex finite algebra, including q=0 and q>m. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

theorem rectangular_minor_product_permutation_invariant {q m : ℕ}
    (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ)
    (f : Fin q → Fin m) (σ : Equiv.Perm (Fin q)) :
    (A.submatrix id (fun i => f (σ i))).det * (B.submatrix (fun i => f (σ i)) id).det =
      (A.submatrix id f).det * (B.submatrix f id).det := by
  have ha : A.submatrix id (fun i => f (σ i)) = (A.submatrix id f).submatrix id σ := rfl
  have hb : B.submatrix (fun i => f (σ i)) id = (B.submatrix f id).submatrix σ id := rfl
  rw [ha,hb,Matrix.det_permute',Matrix.det_permute]
  have hs : (((Equiv.Perm.sign σ : ℤ) : ℂ))*(((Equiv.Perm.sign σ : ℤ) : ℂ))=1 := by
    exact_mod_cast Int.isUnit_mul_self (Equiv.Perm.sign σ).isUnit
  calc
    _ = (((Equiv.Perm.sign σ : ℤ) : ℂ))*(((Equiv.Perm.sign σ : ℤ) : ℂ))*
        ((A.submatrix id f).det * (B.submatrix f id).det) := by ring
    _ = _ := by rw [hs,one_mul]

theorem det_mul_rectangular_sum_cardinal_subsets {q m : ℕ}
    (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ) :
    (A*B).det = ∑ S : {S : Finset (Fin m) // S.card = q},
      (A.submatrix id (fun i => (cardinalSubsetEnumeration S i).val)).det *
        (B.submatrix (fun i => (cardinalSubsetEnumeration S i).val) id).det := by
  classical
  have hg := sum_functions_eq_factorial_sum_cardinal_subsets
    (fun f => (A.submatrix id f).det * (B.submatrix f id).det)
    (fun f hf => by rw [det_submatrix_eq_zero_of_not_injective B f hf,mul_zero])
    (rectangular_minor_product_permutation_invariant A B)
  rw [← det_mul_rectangular_factorial_sum_functions] at hg
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero q)) hg

theorem gram_det_sum_squared_cardinal_minors {m q : ℕ}
    (B : Matrix (Fin m) (Fin q) ℂ) :
    (complexGram B).det = ∑ S : {S : Finset (Fin m) // S.card = q},
      star ((B.submatrix (fun i => (cardinalSubsetEnumeration S i).val) id).det) *
        (B.submatrix (fun i => (cardinalSubsetEnumeration S i).val) id).det := by
  classical
  have h := det_mul_rectangular_sum_cardinal_subsets B.conjTranspose B
  have he (S : {S : Finset (Fin m) // S.card = q}) :
      B.conjTranspose.submatrix id (fun i => (cardinalSubsetEnumeration S i).val) =
      (B.submatrix (fun i => (cardinalSubsetEnumeration S i).val) id).conjTranspose := rfl
  simpa only [he,Matrix.det_conjTranspose,complexGram] using h

end
end JinWishart
#print axioms JinWishart.rectangular_minor_product_permutation_invariant
#print axioms JinWishart.det_mul_rectangular_sum_cardinal_subsets
#print axioms JinWishart.gram_det_sum_squared_cardinal_minors
