import JinWishartFormalization.T3FixedCardinalityRowSelection

/-!
# Permutation-level form of the Theorem 3 determinant coefficient

The fixed-cardinality identity in `T3FixedCardinalityRowSelection` expresses
the paper's sum of mixed-row determinants as one coefficient of a determinant.
This file exposes the same identity after expanding each mixed determinant by
Leibniz permutations. Thus it is an exact algebraic bridge between the
paper's subset-of-rows convention and the coefficient of `det (B + X A)`.
It does not connect this finite sum to the probability integral in Theorem 3.
-/

open Finset

namespace JinWishart

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Leibniz expansion of one mixed-row determinant, with the row choice made
explicit rather than hidden behind `rowMix`. -/
theorem det_rowMix_eq_signedPermutationSum (A B : Matrix n n R) (S : Finset n) :
    (rowMix A B S).det =
      ∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : R) *
          ∏ i, (if i ∈ S then A i (σ i) else B i (σ i)) := by
  rw [det_apply_rows]
  rfl

/-- Fully expanded fixed-cardinality row-selection identity. The inner sum
is the signed permutation formula with `A` used on the selected rows and `B`
on their complement; the outer sum is restricted to exactly `p` selected
rows. By the preceding coefficient theorem, this expression equals the
coefficient of `X^p` in `det (B + X A)`. -/
theorem coeff_det_rowAffinePolynomial_eq_fixedCardPermutationSum
    (A B : Matrix n n R) (p : ℕ) :
    Polynomial.coeff ((rowAffinePolynomialMatrix A B).det) p =
      ∑ S ∈ Finset.univ.powerset,
        (if S.card = p then
          ∑ σ : Equiv.Perm n,
            ((Equiv.Perm.sign σ : ℤ) : R) *
              ∏ i, (if i ∈ S then A i (σ i) else B i (σ i))
         else 0) := by
  rw [coeff_det_rowAffinePolynomial_eq_fixedCardRowSum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hp : S.card = p
  · simp only [hp, ↓reduceIte]
    rw [det_rowMix_eq_signedPermutationSum]
  · simp [hp]

end

end JinWishart
