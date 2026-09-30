import JinWishartFormalization.MvPolynomialZeroSetNull
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The real-coordinate discriminant of a complex 2 × 2 Gram matrix

This is an isolated finite-dimensional prototype.  It proves a real-polynomial null-set result
for the complex 2 × 2 sample matrix parameterized by eight real coordinates.  It does not prove
absolute continuity of a Gaussian law or a general complex Wishart theorem.
-/

namespace JinWishart

open Matrix
open MeasureTheory

noncomputable section

/-- Real/imaginary coordinate index in row-major order for a complex 2 × 2 sample matrix. -/
def complexGramTwoCoord (i j : Fin 2) (isImag : Bool) : Fin 8 :=
  ⟨4 * i.val + 2 * j.val + (if isImag then 1 else 0), by
    cases isImag <;> simp <;> omega⟩

def complexGramTwoReVar (i j : Fin 2) : MvPolynomial (Fin 8) ℝ :=
  MvPolynomial.X (complexGramTwoCoord i j false)

def complexGramTwoImVar (i j : Fin 2) : MvPolynomial (Fin 8) ℝ :=
  MvPolynomial.X (complexGramTwoCoord i j true)

def complexGramTwoG00Poly : MvPolynomial (Fin 8) ℝ :=
  complexGramTwoReVar 0 0 ^ 2 + complexGramTwoImVar 0 0 ^ 2 +
    complexGramTwoReVar 1 0 ^ 2 + complexGramTwoImVar 1 0 ^ 2

def complexGramTwoG11Poly : MvPolynomial (Fin 8) ℝ :=
  complexGramTwoReVar 0 1 ^ 2 + complexGramTwoImVar 0 1 ^ 2 +
    complexGramTwoReVar 1 1 ^ 2 + complexGramTwoImVar 1 1 ^ 2

def complexGramTwoG01RePoly : MvPolynomial (Fin 8) ℝ :=
  complexGramTwoReVar 0 0 * complexGramTwoReVar 0 1 +
    complexGramTwoImVar 0 0 * complexGramTwoImVar 0 1 +
    complexGramTwoReVar 1 0 * complexGramTwoReVar 1 1 +
    complexGramTwoImVar 1 0 * complexGramTwoImVar 1 1

def complexGramTwoG01ImPoly : MvPolynomial (Fin 8) ℝ :=
  complexGramTwoReVar 0 0 * complexGramTwoImVar 0 1 -
    complexGramTwoImVar 0 0 * complexGramTwoReVar 0 1 +
    complexGramTwoReVar 1 0 * complexGramTwoImVar 1 1 -
    complexGramTwoImVar 1 0 * complexGramTwoReVar 1 1

/-- The requested real polynomial `(g₀₀-g₁₁)² + 4(|Re g₀₁|²+|Im g₀₁|²)`. -/
def complexGramTwoDiscPoly : MvPolynomial (Fin 8) ℝ :=
  (complexGramTwoG00Poly - complexGramTwoG11Poly) ^ 2 +
    4 * (complexGramTwoG01RePoly ^ 2 + complexGramTwoG01ImPoly ^ 2)

/-- The complex sample matrix represented by eight real coordinates. -/
def complexGramTwoSample (x : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ⟨x (complexGramTwoCoord i j false), x (complexGramTwoCoord i j true)⟩

/-- The Hermitian column Gram matrix of the complex sample. -/
def complexGramTwoGram (x : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (complexGramTwoSample x)ᴴ * complexGramTwoSample x

/-- The four entries of the complex Gram matrix written directly from real coordinates. -/
def complexGramTwoGramExplicit (x : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = 0 then
      if j = 0 then Complex.ofReal (MvPolynomial.eval x complexGramTwoG00Poly)
      else Complex.ofReal (MvPolynomial.eval x complexGramTwoG01RePoly) +
        Complex.I * Complex.ofReal (MvPolynomial.eval x complexGramTwoG01ImPoly)
    else if j = 0 then
      star (Complex.ofReal (MvPolynomial.eval x complexGramTwoG01RePoly) +
        Complex.I * Complex.ofReal (MvPolynomial.eval x complexGramTwoG01ImPoly))
    else Complex.ofReal (MvPolynomial.eval x complexGramTwoG11Poly)

/-- The matrix product `XᴴX` has the expected explicit Hermitian entries. -/
theorem complexGramTwoGram_eq_explicit (x : Fin 8 → ℝ) :
    complexGramTwoGram x = complexGramTwoGramExplicit x := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [complexGramTwoGram, complexGramTwoSample, complexGramTwoGramExplicit,
      complexGramTwoG00Poly, complexGramTwoG11Poly, complexGramTwoG01RePoly,
      complexGramTwoG01ImPoly, complexGramTwoReVar, complexGramTwoImVar,
      complexGramTwoCoord, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
      RCLike.star_def] <;> ring

/-- The discriminant of the explicit Hermitian matrix is real and has the expected formula. -/
theorem complexGramTwoGramExplicit_discr (x : Fin 8 → ℝ) :
    Matrix.discr (complexGramTwoGramExplicit x) =
      Complex.ofReal ((MvPolynomial.eval x complexGramTwoG00Poly -
        MvPolynomial.eval x complexGramTwoG11Poly) ^ 2 +
        4 * ((MvPolynomial.eval x complexGramTwoG01RePoly) ^ 2 +
          (MvPolynomial.eval x complexGramTwoG01ImPoly) ^ 2)) := by
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [complexGramTwoGramExplicit, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, RCLike.star_def] <;> ring_nf

/-- Evaluation of the real polynomial gives the real part of the complex Gram discriminant. -/
theorem eval_complexGramTwoDiscPoly_eq_matrix_discr_re (x : Fin 8 → ℝ) :
    MvPolynomial.eval x complexGramTwoDiscPoly =
      (Matrix.discr (complexGramTwoGram x)).re := by
  rw [complexGramTwoGram_eq_explicit, complexGramTwoGramExplicit_discr]
  simp only [Complex.ofReal_re]
  simp [complexGramTwoDiscPoly, map_sub, map_add, map_mul, map_pow]

/-- The complex Gram discriminant has zero imaginary part. -/
theorem complexGramTwo_matrixDiscr_im_eq_zero (x : Fin 8 → ℝ) :
    (Matrix.discr (complexGramTwoGram x)).im = 0 := by
  rw [complexGramTwoGram_eq_explicit, complexGramTwoGramExplicit_discr]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_sub, ← Complex.ofReal_add,
    ← Complex.ofReal_mul, Complex.ofReal_im]

/-- Thus vanishing of the complex matrix discriminant is exactly the real polynomial zero set. -/
theorem complexGramTwo_matrixDiscr_eq_zero_iff (x : Fin 8 → ℝ) :
    Matrix.discr (complexGramTwoGram x) = 0 ↔
      MvPolynomial.eval x complexGramTwoDiscPoly = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simpa only [Complex.zero_re, ← eval_complexGramTwoDiscPoly_eq_matrix_discr_re] using hre
  · intro h
    apply Complex.ext
    · simpa only [Complex.zero_re, ← eval_complexGramTwoDiscPoly_eq_matrix_discr_re] using h
    · exact complexGramTwo_matrixDiscr_im_eq_zero x

/-- The diagonal sample `diag(1,2)` witnesses that the eight-variable polynomial is nonzero. -/
theorem eval_complexGramTwoDiscPoly_diagonalWitness :
    MvPolynomial.eval (fun i : Fin 8 => if i = 0 then 1 else if i = 6 then 2 else 0)
      complexGramTwoDiscPoly = 9 := by
  norm_num [complexGramTwoDiscPoly, complexGramTwoG00Poly, complexGramTwoG11Poly,
    complexGramTwoG01RePoly, complexGramTwoG01ImPoly, complexGramTwoReVar,
    complexGramTwoImVar, complexGramTwoCoord]

theorem complexGramTwoDiscPoly_ne_zero : complexGramTwoDiscPoly ≠ 0 := by
  intro h
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 8 => if i = 0 then 1 else if i = 6 then 2 else 0)) h
  rw [eval_complexGramTwoDiscPoly_diagonalWitness] at heval
  norm_num at heval

/-- The zero set of the eight-coordinate real polynomial has Lebesgue measure zero. -/
theorem complexGramTwoDiscPoly_zeroSet_volume_eq_zero :
    volume {x : Fin 8 → ℝ | MvPolynomial.eval x complexGramTwoDiscPoly = 0} = 0 :=
  mvPolynomial_zeroSet_volume_eq_zero 8 complexGramTwoDiscPoly complexGramTwoDiscPoly_ne_zero

/-- The parameter set where the complex 2 × 2 Gram matrix has zero discriminant is null. -/
theorem complexGramTwo_matrixDiscr_zeroSet_volume_eq_zero :
    volume {x : Fin 8 → ℝ | Matrix.discr (complexGramTwoGram x) = 0} = 0 := by
  have hset : {x : Fin 8 → ℝ | Matrix.discr (complexGramTwoGram x) = 0} =
      {x : Fin 8 → ℝ | MvPolynomial.eval x complexGramTwoDiscPoly = 0} := by
    ext x
    exact complexGramTwo_matrixDiscr_eq_zero_iff x
  rw [hset]
  exact complexGramTwoDiscPoly_zeroSet_volume_eq_zero

end

end JinWishart
