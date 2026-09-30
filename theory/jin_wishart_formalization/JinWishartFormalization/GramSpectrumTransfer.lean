import JinWishartFormalization.PaperSmallSideGram
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Transfer of the nonzero Gram spectrum between the two orientations

For a rectangular complex matrix `A : Matrix (Fin m) (Fin n) ℂ` with `n ≤ m`, the
two Gram orientations `Aᴴ * A` (`n × n`) and `A * Aᴴ` (`m × m`) have the same
nonzero eigenvalues with the same multiplicities.  Mathlib supplies the
characteristic-polynomial relation

`(A * Aᴴ).charpoly = X ^ (m - n) * (Aᴴ * A).charpoly`  (`Matrix.charpoly_mul_comm_of_le`),

so the only difference is the forced zero eigenvalue of multiplicity `m - n` on
the larger side.

This is the "nonzero spectrum correspondence" that `theory/README.md` and the G1
note recorded as not yet formalized.  It matters because the paper states every
eigenvalue distribution for the small side `s = min(m, n)` Gram matrix, while the
probability model computes `XᴴX`.

Everything here is deterministic linear algebra over `ℂ`; no probability enters.
-/

open Matrix Polynomial

namespace JinWishart

noncomputable section

variable {m n : ℕ}

/-- **Characteristic polynomials of the two Gram orientations.** For `n ≤ m`,
the larger Gram's characteristic polynomial is `X ^ (m - n)` times the smaller
one's. -/
theorem charpoly_rowGram_eq_X_pow_mul_charpoly_colGram
    (A : Matrix (Fin m) (Fin n) ℂ) (hle : n ≤ m) :
    (A * Aᴴ).charpoly = X ^ (m - n) * (Aᴴ * A).charpoly := by
  have h := Matrix.charpoly_mul_comm_of_le A (Aᴴ) (by simpa using hle)
  simpa [Matrix.conjTranspose_conjTranspose] using h

/-- The same relation read on root multisets, exposing the extra zero
eigenvalues of the larger side. -/
theorem roots_rowGram_eq_nsmul_zero_add_roots_colGram
    (A : Matrix (Fin m) (Fin n) ℂ) (hle : n ≤ m) :
    (A * Aᴴ).charpoly.roots = (m - n) • ({0} : Multiset ℂ) + (Aᴴ * A).charpoly.roots := by
  have hne1 : (X ^ (m - n) : ℂ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hne2 : (Aᴴ * A).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  rw [charpoly_rowGram_eq_X_pow_mul_charpoly_colGram A hle,
    Polynomial.roots_mul (mul_ne_zero hne1 hne2), Polynomial.roots_X_pow]

/-- **Nonzero eigenvalues agree, with multiplicity.** This is the precise sense
in which the two Gram orientations carry the same spectral information. -/
theorem roots_count_eq_of_ne_zero (A : Matrix (Fin m) (Fin n) ℂ) (hle : n ≤ m)
    {z : ℂ} (hz : z ≠ 0) :
    ((A * Aᴴ).charpoly.roots).count z = ((Aᴴ * A).charpoly.roots).count z := by
  rw [roots_rowGram_eq_nsmul_zero_add_roots_colGram A hle, Multiset.count_add]
  have hzero : ((m - n) • ({0} : Multiset ℂ)).count z = 0 := by
    rw [Multiset.count_nsmul, Multiset.count_singleton]
    simp [hz]
  rw [hzero, zero_add]

/-- The larger Gram has exactly `m - n` more zero eigenvalues than the smaller
one. -/
theorem count_zero_rowGram_eq_add (A : Matrix (Fin m) (Fin n) ℂ) (hle : n ≤ m) :
    ((A * Aᴴ).charpoly.roots).count 0 =
      (m - n) + ((Aᴴ * A).charpoly.roots).count 0 := by
  rw [roots_rowGram_eq_nsmul_zero_add_roots_colGram A hle, Multiset.count_add,
    Multiset.count_nsmul, Multiset.count_singleton]
  simp

/-- The paper's small-side Gram matrix has the same characteristic polynomial
as the `XᴴX` orientation.  Combined with
`roots_count_eq_of_ne_zero`, the small-side spectrum is exactly the nonzero part
of the `XXᴴ` spectrum. -/
theorem charpoly_paperSmallSideGram_eq_charpoly_colGram
    (A : Matrix (Fin m) (Fin n) ℂ) (hle : n ≤ m) :
    (paperSmallSideGram A).charpoly = (Aᴴ * A).charpoly := by
  by_cases hmn : m ≤ n
  · have hEq : m = n := le_antisymm hmn hle
    subst hEq
    rw [paperSmallSideGram, dif_pos le_rfl, charpoly_submatrix_equiv,
      Matrix.charpoly_mul_comm]
  · rw [paperSmallSideGram, dif_neg hmn, charpoly_submatrix_equiv]

end

end JinWishart
