import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Eigenvector transfer between the two rectangular Gram orientations

For rectangular matrices, multiplication by `A` transfers an eigenvector of
`B A` to an eigenvector of `A B` at the same eigenvalue.  When that eigenvalue
is nonzero, the transferred vector cannot vanish.  Specializing `B = Aᴴ`
gives the two directions between the nonzero eigenspaces of `Aᴴ A` and
`A Aᴴ`.  This is a direct matrix-vector proof; it does not assume or define a
singular-value decomposition.
-/

namespace JinWishart

open scoped Matrix

section Rectangular

variable {m n : ℕ}

/-- If `v` is an eigenvector of `B*A` with eigenvalue `μ`, then `A*v` is an
eigenvector of `A*B` with the same eigenvalue. -/
theorem rectangular_mulVec_eigenvector_transfer
    (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ)
    (v : Fin n → ℂ) (μ : ℂ)
    (hv : (B * A).mulVec v = μ • v) :
    (A * B).mulVec (A.mulVec v) = μ • (A.mulVec v) := by
  have hfactor :
      (A * B).mulVec (A.mulVec v) = A.mulVec ((B * A).mulVec v) := by
    calc
      (A * B).mulVec (A.mulVec v) = ((A * B) * A).mulVec v := by
        exact Matrix.mulVec_mulVec v (A * B) A
      _ = (A * (B * A)).mulVec v := by rw [Matrix.mul_assoc]
      _ = A.mulVec ((B * A).mulVec v) :=
        (Matrix.mulVec_mulVec v A (B * A)).symm
  calc
    (A * B).mulVec (A.mulVec v) = A.mulVec ((B * A).mulVec v) := hfactor
    _ = A.mulVec (μ • v) := by rw [hv]
    _ = μ • (A.mulVec v) := by rw [Matrix.mulVec_smul]

/-- At a nonzero eigenvalue, the eigenvector transfer above never maps a
nonzero vector to zero. -/
theorem rectangular_mulVec_eigenvector_transfer_ne_zero
    (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ)
    (v : Fin n → ℂ) (μ : ℂ)
    (hv : (B * A).mulVec v = μ • v)
    (hμ : μ ≠ 0) (hv0 : v ≠ 0) :
    A.mulVec v ≠ 0 := by
  intro hAv
  have hBA : (B * A).mulVec v = 0 := by
    calc
      (B * A).mulVec v = B.mulVec (A.mulVec v) :=
        (Matrix.mulVec_mulVec v B A).symm
      _ = B.mulVec 0 := by rw [hAv]
      _ = 0 := Matrix.mulVec_zero B
  have hμv : μ • v = 0 := by rw [← hv, hBA]
  exact hv0 ((smul_eq_zero.mp hμv).resolve_left hμ)

/-- An eigenvector of the column Gram matrix `Aᴴ*A` transfers through `A` to
an eigenvector of the row Gram matrix `A*Aᴴ`, preserving its eigenvalue. -/
theorem colGram_eigenvector_to_rowGram
    (A : Matrix (Fin m) (Fin n) ℂ)
    (v : Fin n → ℂ) (μ : ℂ)
    (hv : (Aᴴ * A).mulVec v = μ • v) :
    (A * Aᴴ).mulVec (A.mulVec v) = μ • (A.mulVec v) :=
  rectangular_mulVec_eigenvector_transfer A Aᴴ v μ hv

/-- Conversely, an eigenvector of `A*Aᴴ` transfers through `Aᴴ` to an
eigenvector of `Aᴴ*A` at the same eigenvalue. -/
theorem rowGram_eigenvector_to_colGram
    (A : Matrix (Fin m) (Fin n) ℂ)
    (v : Fin m → ℂ) (μ : ℂ)
    (hv : (A * Aᴴ).mulVec v = μ • v) :
    (Aᴴ * A).mulVec (Aᴴ.mulVec v) = μ • (Aᴴ.mulVec v) := by
  exact rectangular_mulVec_eigenvector_transfer Aᴴ A v μ hv

/-- The two Gram transfers are injective on nonzero-eigenvalue eigenspaces. -/
theorem colGram_eigenvector_to_rowGram_ne_zero
    (A : Matrix (Fin m) (Fin n) ℂ)
    (v : Fin n → ℂ) (μ : ℂ)
    (hv : (Aᴴ * A).mulVec v = μ • v)
    (hμ : μ ≠ 0) (hv0 : v ≠ 0) :
    A.mulVec v ≠ 0 :=
  rectangular_mulVec_eigenvector_transfer_ne_zero A Aᴴ v μ hv hμ hv0

/-- Nonzero eigenvectors transfer back from row Gram to column Gram. -/
theorem rowGram_eigenvector_to_colGram_ne_zero
    (A : Matrix (Fin m) (Fin n) ℂ)
    (v : Fin m → ℂ) (μ : ℂ)
    (hv : (A * Aᴴ).mulVec v = μ • v)
    (hμ : μ ≠ 0) (hv0 : v ≠ 0) :
    Aᴴ.mulVec v ≠ 0 := by
  apply rectangular_mulVec_eigenvector_transfer_ne_zero Aᴴ A v μ hv hμ hv0

end Rectangular

end JinWishart
