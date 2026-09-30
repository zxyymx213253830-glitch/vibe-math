import JinWishartFormalization.DeterminantRowExpansion
import Mathlib.Algebra.Polynomial.Coeff

/-!
# The fixed-cardinality determinant sum in Theorem 3

For matrices `A` and `B`, the paper's `Theta` construction selects exactly
`p = k - 1` rows from the `Psi` block and all remaining rows from the `Xi`
block. This file identifies that fixed-cardinality sum as a polynomial
coefficient of `det (B + X A)`. A diagonal row-selector mask proves the
individual summands have degree exactly the number of selected rows.

This is only the determinant combinatorics in (23)--(25), not the probability
integral, ordered-eigenvalue event, or Wishart normalization in (22)--(24).
-/

open Finset

namespace JinWishart

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- The polynomial matrix whose `i`th row is the affine combination of the
`i`th rows of `B` and `A`. -/
def rowAffinePolynomialMatrix (A B : Matrix n n R) :
    Matrix n n (Polynomial R) :=
  fun i j => Polynomial.C (B i j) + Polynomial.X * Polynomial.C (A i j)

/-- A diagonal selector scaling precisely the rows indexed by `S` by `X`.
Multiplying it by the constant row-mix matrix is the structured block-mask
representation of a `Theta` summand. -/
def rowSelectionMask (S : Finset n) : Matrix n n (Polynomial R) :=
  Matrix.diagonal (fun i => if i ∈ S then Polynomial.X else 1)

private theorem det_polynomialRowMix (A B : Matrix n n R) (S : Finset n) :
    (rowMix
      (fun i j => Polynomial.X * Polynomial.C (A i j))
      (fun i j => Polynomial.C (B i j)) S).det =
        Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det) := by
  let D := rowSelectionMask (R := R) S
  let M : Matrix n n (Polynomial R) := fun i j => Polynomial.C (rowMix A B S i j)
  let Q : Matrix n n (Polynomial R) :=
    Matrix.diagonal (fun r => if r ∈ S then Polynomial.X else 1) * M
  have hmat : rowMix
        (fun i j => Polynomial.X * Polynomial.C (A i j))
      (fun i j => Polynomial.C (B i j)) S = Q := by
    apply Matrix.ext
    intro i j
    change (if i ∈ S then Polynomial.X * Polynomial.C (A i j)
      else Polynomial.C (B i j)) = Q i j
    have hQ : Q = D * M := by rfl
    rw [hQ, show D = Matrix.diagonal (fun r => if r ∈ S then Polynomial.X else 1) by rfl,
      Matrix.diagonal_mul]
    by_cases hi : i ∈ S <;> simp [M, rowMix, hi]
  have hdetM : M.det = Polynomial.C ((rowMix A B S).det) := by
    dsimp [M]
    exact (Polynomial.C.map_det (rowMix A B S)).symm
  rw [hmat]
  change (D * M).det =
    Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det)
  rw [Matrix.det_mul, hdetM]
  simp [D, rowSelectionMask, Matrix.det_diagonal, Finset.prod_ite_mem]

/-- Determinant form of the `Theta` row mixture: selecting a row subset `S`
from `A` and its complement from `B` contributes `X^|S|` times that selected
minor determinant to `det (B + X A)`. -/
theorem det_rowAffinePolynomial_eq_sum_rowMix
    (A B : Matrix n n R) :
    (rowAffinePolynomialMatrix A B).det =
      ∑ S ∈ Finset.univ.powerset,
        Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det) := by
  have hsum := det_add_eq_sum_rowMix
    (fun i j => Polynomial.X * Polynomial.C (A i j))
    (fun i j => Polynomial.C (B i j))
  let P : Matrix n n (Polynomial R) :=
    (fun i j => Polynomial.X * Polynomial.C (A i j)) +
      (fun i j => Polynomial.C (B i j))
  have hrow : rowAffinePolynomialMatrix A B = P := by
    apply Matrix.ext
    intro i j
    change Polynomial.C (B i j) + Polynomial.X * Polynomial.C (A i j) =
      Polynomial.X * Polynomial.C (A i j) + Polynomial.C (B i j)
    ring
  have hsum' : P.det =
        ∑ S ∈ Finset.univ.powerset,
          Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det) := by
    have hs : P.det = ∑ S ∈ Finset.univ.powerset,
        (rowMix (fun i j => Polynomial.X * Polynomial.C (A i j))
          (fun i j => Polynomial.C (B i j)) S).det := by
      dsimp [P]
      exact hsum
    rw [hs]
    apply Finset.sum_congr rfl
    intro S hS
    exact det_polynomialRowMix A B S
  calc
    (rowAffinePolynomialMatrix A B).det = P.det := by rw [hrow]
    _ = _ := hsum'

/-- Fixed-cardinality row-selection identity, written as a zero-padded subset
sum. The coefficient of `X^p` in
the determinant of the affine row-block matrix is exactly the sum of the
determinants obtained by choosing `p` rows from `A` (the `Psi` block) and the
remaining rows from `B` (the `Xi` block). -/
theorem coeff_det_rowAffinePolynomial_eq_fixedCardRowSum
    (A B : Matrix n n R) (p : ℕ) :
    Polynomial.coeff ((rowAffinePolynomialMatrix A B).det) p =
      ∑ S ∈ Finset.univ.powerset,
        (if S.card = p then (rowMix A B S).det else 0) := by
  rw [det_rowAffinePolynomial_eq_sum_rowMix]
  have hmap :
      Polynomial.coeff
          (∑ S ∈ Finset.univ.powerset,
            Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det)) p =
        ∑ S ∈ Finset.univ.powerset,
          Polynomial.coeff
            (Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det)) p := by
    change (Polynomial.lcoeff R p)
        (∑ S ∈ Finset.univ.powerset,
          Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det)) = _
    rw [map_sum]
    simp only [Polynomial.lcoeff_apply]
  rw [hmap]
  have hterms :
      ∑ S ∈ Finset.univ.powerset,
        Polynomial.coeff
          (Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det)) p =
        ∑ S ∈ Finset.univ.powerset,
          (if S.card = p then (rowMix A B S).det else 0) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [show Polynomial.X ^ S.card * Polynomial.C ((rowMix A B S).det) =
          Polynomial.C ((rowMix A B S).det) * Polynomial.X ^ S.card by
        rw [mul_comm]]
    rw [Polynomial.coeff_C_mul_X_pow]
    simp [eq_comm]
  rw [hterms]

end

end JinWishart
