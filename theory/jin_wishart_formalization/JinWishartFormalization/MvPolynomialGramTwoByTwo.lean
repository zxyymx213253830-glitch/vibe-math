import JinWishartFormalization.MvPolynomialZeroSetNull
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A real 2 × 2 Gram-discriminant polynomial prototype

This file isolates the four-coordinate real sample matrix case.  It does not establish the
corresponding complex/noncentral Wishart statement or connect the polynomial to a Gaussian law.
-/

namespace JinWishart

open Matrix
open MeasureTheory

noncomputable section

/-- Flatten a 2 × 2 coordinate pair in row-major order to `Fin 4`. -/
def gramTwoCoord (i j : Fin 2) : Fin 4 :=
  ⟨2 * i.val + j.val, by omega⟩

/-- The generic real sample matrix whose four entries are coordinate indeterminates. -/
def gramTwoSamplePoly : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) ℝ) :=
  fun i j => MvPolynomial.X (gramTwoCoord i j)

/-- The column Gram matrix over the polynomial ring. -/
def gramTwoGramPoly : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) ℝ) :=
  gramTwoSamplePolyᵀ * gramTwoSamplePoly

def gramTwoG00Poly : MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 2 ^ 2

def gramTwoG11Poly : MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.X 1 ^ 2 + MvPolynomial.X 3 ^ 2

def gramTwoG01Poly : MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 2 * MvPolynomial.X 3

/-- Explicit polynomial formula for the discriminant of `Xᵀ X` in the four sample coordinates. -/
def gramTwoDiscPoly : MvPolynomial (Fin 4) ℝ :=
  (gramTwoG00Poly - gramTwoG11Poly) ^ 2 + 4 * gramTwoG01Poly ^ 2

/-- The explicit polynomial is the matrix discriminant of the generic polynomial Gram matrix. -/
theorem gramTwoDiscPoly_eq_polynomial_matrix_discr :
    gramTwoDiscPoly = Matrix.discr gramTwoGramPoly := by
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [gramTwoDiscPoly, gramTwoG00Poly, gramTwoG11Poly, gramTwoG01Poly,
    gramTwoGramPoly, gramTwoSamplePoly, gramTwoCoord, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two]
  ring

/-- Interpret four real coordinates as a 2 × 2 sample matrix. -/
def gramTwoSample (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => x (gramTwoCoord i j)

/-- Its column Gram matrix. -/
def gramTwoGram (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (gramTwoSample x)ᵀ * gramTwoSample x

/-- Evaluation of the explicit polynomial is the matrix discriminant of the real Gram matrix. -/
theorem eval_gramTwoDiscPoly_eq_matrix_discr (x : Fin 4 → ℝ) :
    MvPolynomial.eval x gramTwoDiscPoly = Matrix.discr (gramTwoGram x) := by
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [gramTwoDiscPoly, gramTwoG00Poly, gramTwoG11Poly, gramTwoG01Poly,
    gramTwoGram, gramTwoSample, gramTwoCoord, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two]
  ring

/-- A diagonal witness evaluates the discriminant polynomial to `9`. -/
theorem eval_gramTwoDiscPoly_diagonalWitness :
    MvPolynomial.eval (fun i : Fin 4 => if i = 0 then 1 else if i = 3 then 2 else 0)
      gramTwoDiscPoly = 9 := by
  norm_num [gramTwoDiscPoly, gramTwoG00Poly, gramTwoG11Poly, gramTwoG01Poly]

/-- The four-coordinate Gram-discriminant polynomial is nonzero. -/
theorem gramTwoDiscPoly_ne_zero : gramTwoDiscPoly ≠ 0 := by
  intro h
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 4 => if i = 0 then 1 else if i = 3 then 2 else 0)) h
  rw [eval_gramTwoDiscPoly_diagonalWitness] at heval
  norm_num at heval

/-- The zero set of the real 2 × 2 Gram-discriminant polynomial is Lebesgue-null. -/
theorem gramTwoDiscPoly_zeroSet_volume_eq_zero :
    volume {x : Fin 4 → ℝ | MvPolynomial.eval x gramTwoDiscPoly = 0} = 0 :=
  mvPolynomial_zeroSet_volume_eq_zero 4 gramTwoDiscPoly gramTwoDiscPoly_ne_zero

/-- The parameter set where the real 2 × 2 Gram matrix has zero matrix-discriminant is null. -/
theorem gramTwo_matrixDiscr_zeroSet_volume_eq_zero :
    volume {x : Fin 4 → ℝ | Matrix.discr (gramTwoGram x) = 0} = 0 := by
  have hset : {x : Fin 4 → ℝ | Matrix.discr (gramTwoGram x) = 0} =
      {x : Fin 4 → ℝ | MvPolynomial.eval x gramTwoDiscPoly = 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      rw [← eval_gramTwoDiscPoly_eq_matrix_discr x] at hx
      exact hx
    · intro hx
      rw [eval_gramTwoDiscPoly_eq_matrix_discr x] at hx
      exact hx
  rw [hset]
  exact gramTwoDiscPoly_zeroSet_volume_eq_zero

end

end JinWishart
