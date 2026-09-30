import JinWishartFormalization.MvPolynomialZeroSetNull
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable

/-!
# Repeated eigenvalues of real matrices form a null set

For a square matrix over a field, an eigenvalue of multiplicity at least two is a
common root of the characteristic polynomial and of its derivative, so the
resultant of the two polynomials vanishes.  The resultant of the characteristic
polynomial of the *generic* `d × d` matrix is a polynomial in the `d²` entries,
and it is not the zero polynomial: evaluated at a diagonal matrix with pairwise
distinct entries it gives a nonzero value (that characteristic polynomial is
separable).  Combining this with `mvPolynomial_zeroSet_volume_eq_zero`, the set of
real `d × d` matrices whose characteristic polynomial has a multiple real root is
Lebesgue-null.

This is the general-dimension multivariate discriminant brick needed by the joint
eigenvalue density work (card G2): outside a null set the spectrum is simple.

Scope: real matrices only.  The complex Hermitian case used for the paper's Gram
matrices needs the additional split of the resultant into real and imaginary
parts and is not treated here.
-/

open Matrix Polynomial MeasureTheory

namespace JinWishart

/-- Flatten a pair of `Fin d` indices to `Fin (d * d)` in row-major order. -/
def matIdx (d : ℕ) (i j : Fin d) : Fin (d * d) :=
  ⟨i.1 * d + j.1, by
    have hi : i.1 < d := i.2
    have hj : j.1 < d := j.2
    have h1 : i.1 * d + j.1 ≤ i.1 * d + d := by omega
    have h2 : i.1 * d + d = (i.1 + 1) * d := by ring
    have h3 : (i.1 + 1) * d ≤ d * d := Nat.mul_le_mul (by omega) le_rfl
    omega⟩

/-- The generic `d × d` real matrix: the entry `(i, j)` is the indeterminate
`X (matIdx d i j)`. -/
noncomputable def genericMatrix (d : ℕ) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin (d * d)) ℝ) :=
  fun i j => MvPolynomial.X (matIdx d i j)

/-- The real matrix encoded by `d * d` coordinates (row-major). -/
def matrixFromCoords (d : ℕ) (x : Fin (d * d) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => x (matIdx d i j)

/-- Resultant of the characteristic polynomial of the generic matrix with its
derivative.  For a real matrix `A` this polynomial evaluated at the entries of
`A` is the resultant of `A.charpoly` with its derivative, which vanishes exactly
when the characteristic polynomial has a multiple root. -/
noncomputable def genericResultant (d : ℕ) : MvPolynomial (Fin (d * d)) ℝ :=
  resultant (genericMatrix d).charpoly (genericMatrix d).charpoly.derivative d (d - 1)

/-- Evaluating the generic resultant at the coordinates of a matrix recovers the
resultant of that matrix's characteristic polynomial with its derivative. -/
theorem genericResultant_eval (d : ℕ) (x : Fin (d * d) → ℝ) :
    MvPolynomial.eval x (genericResultant d)
      = resultant (matrixFromCoords d x).charpoly (matrixFromCoords d x).charpoly.derivative := by
  have hmap : (genericMatrix d).map (MvPolynomial.eval x) = matrixFromCoords d x := by
    ext i j
    simp [genericMatrix, matrixFromCoords, Matrix.map_apply, matIdx, MvPolynomial.eval_X]
  have hcp : (matrixFromCoords d x).charpoly
      = ((genericMatrix d).charpoly).map (MvPolynomial.eval x) := by
    rw [← hmap, charpoly_map]
  have hdv : (matrixFromCoords d x).charpoly.derivative
      = ((genericMatrix d).charpoly.derivative).map (MvPolynomial.eval x) := by
    rw [hcp, derivative_map]
  have hnd1 : (matrixFromCoords d x).charpoly.natDegree = d := by
    simp
  have hnd2 : (matrixFromCoords d x).charpoly.derivative.natDegree = d - 1 := by
    rw [Polynomial.natDegree_derivative, hnd1]
  have hkey : resultant (matrixFromCoords d x).charpoly (matrixFromCoords d x).charpoly.derivative
        d (d - 1)
      = resultant (matrixFromCoords d x).charpoly (matrixFromCoords d x).charpoly.derivative := by
    rw [hnd1, hnd2]
  unfold genericResultant
  rw [← hkey, hdv, hcp, resultant_map_map]

/-- A common root of `g` and its derivative forces the resultant to vanish. -/
theorem resultant_eq_zero_of_common_root {K : Type*} [Field K] {f g : K[X]} {t : K}
    (hg0 : g ≠ 0) (hf : f.IsRoot t) (hg : g.IsRoot t) :
    resultant f g = 0 := by
  rw [resultant_eq_zero_iff]
  refine ⟨Or.inr hg0, ?_⟩
  intro hcop
  obtain ⟨a, b, hab⟩ := hcop
  have hd1 : (X - C t : K[X]) ∣ f := dvd_iff_isRoot.mpr hf
  have hd2 : (X - C t : K[X]) ∣ g := dvd_iff_isRoot.mpr hg
  have hone : (X - C t : K[X]) ∣ 1 := by
    have hsum := dvd_add (dvd_mul_of_dvd_left hd1 a) (dvd_mul_of_dvd_left hd2 b)
    have heq : f * a + g * b = a * f + b * g := by ring
    rw [heq, hab] at hsum
    exact hsum
  exact Polynomial.not_isUnit_X_sub_C t (isUnit_of_dvd_one hone)

/-- Coordinates of the diagonal witness matrix with entries `1, 2, …, d`. -/
def diagWitnessCoords (d : ℕ) : Fin (d * d) → ℝ :=
  fun k => if k.1 % d = k.1 / d then ((k.1 / d : ℕ) : ℝ) + 1 else 0

theorem matrixFromCoords_diagWitness (d : ℕ) :
    matrixFromCoords d (diagWitnessCoords d)
      = diagonal (fun i : Fin d => (i : ℝ) + 1) := by
  ext i j
  have hi : i.1 < d := i.2
  have hj : j.1 < d := j.2
  have hmod : (i.1 * d + j.1) % d = j.1 := Nat.mul_add_mod_of_lt hj
  have hdiv : (i.1 * d + j.1) / d = i.1 := by
    have h : (d * i.1 + j.1) / d = i.1 + j.1 / d := Nat.mul_add_div (by omega) i.1 j.1
    rw [Nat.mul_comm, h, Nat.div_eq_of_lt hj, Nat.add_zero]
  simp only [matrixFromCoords, diagWitnessCoords, matIdx, Matrix.diagonal_apply, hmod, hdiv]
  by_cases h : i = j
  · subst h
    simp
  · have hne : (j.1 : ℕ) ≠ i.1 := fun heq => h (Fin.ext heq.symm)
    simp [hne, h]

/-- The generic resultant is a nonzero polynomial: the diagonal witness matrix
has pairwise distinct eigenvalues, so its characteristic polynomial is
separable and the resultant does not vanish. -/
theorem genericResultant_ne_zero (d : ℕ) (hd : 0 < d) : genericResultant d ≠ 0 := by
  intro hzero
  have key := genericResultant_eval d (diagWitnessCoords d)
  rw [hzero, map_zero] at key
  rw [matrixFromCoords_diagWitness] at key
  have hsep : Polynomial.Separable (diagonal (fun i : Fin d => (i : ℝ) + 1)).charpoly := by
    rw [Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    intro i j h
    have hj : (i : ℝ) = (j : ℝ) := by simpa using h
    have : i.val = j.val := by exact_mod_cast hj
    exact Fin.ext this
  -- `Polynomial.Separable` is by definition `IsCoprime f f.derivative`.
  have hcop : IsCoprime (diagonal (fun i : Fin d => (i : ℝ) + 1)).charpoly
      (diagonal (fun i : Fin d => (i : ℝ) + 1)).charpoly.derivative := hsep
  exact resultant_ne_zero _ _ hcop key.symm

/-- The set of real `d × d` matrices whose characteristic polynomial has a
multiple real root is Lebesgue-null. -/
theorem repeated_root_set_null (d : ℕ) (hd : 0 < d) :
    volume {x : Fin (d * d) → ℝ |
      ∃ t : ℝ, 1 < ((matrixFromCoords d x).charpoly).rootMultiplicity t} = 0 := by
  have hnull : volume {x : Fin (d * d) → ℝ | MvPolynomial.eval x (genericResultant d) = 0} = 0 :=
    mvPolynomial_zeroSet_volume_eq_zero (d * d) (genericResultant d)
      (genericResultant_ne_zero d hd)
  have hsub : {x : Fin (d * d) → ℝ |
      ∃ t : ℝ, 1 < ((matrixFromCoords d x).charpoly).rootMultiplicity t}
      ⊆ {x : Fin (d * d) → ℝ | MvPolynomial.eval x (genericResultant d) = 0} := by
    intro x hx
    obtain ⟨t, ht⟩ := hx
    have hnd : (matrixFromCoords d x).charpoly.natDegree = d := by
      simpa using Matrix.charpoly_natDegree_eq_dim (matrixFromCoords d x)
    have hder : (matrixFromCoords d x).charpoly.derivative ≠ 0 := by
      rw [Polynomial.derivative_ne_zero, hnd]
      exact hd.ne'
    have hroot : (matrixFromCoords d x).charpoly.IsRoot t := by
      have h := isRoot_iterate_derivative_of_lt_rootMultiplicity
        (p := (matrixFromCoords d x).charpoly) (t := t) (n := 0) (by omega)
      simpa using h
    have hroot' : (matrixFromCoords d x).charpoly.derivative.IsRoot t := by
      have h := isRoot_iterate_derivative_of_lt_rootMultiplicity
        (p := (matrixFromCoords d x).charpoly) (t := t) (n := 1) ht
      simpa using h
    have hres : resultant (matrixFromCoords d x).charpoly
        (matrixFromCoords d x).charpoly.derivative = 0 :=
      resultant_eq_zero_of_common_root hder hroot hroot'
    simp only [Set.mem_ofPred_eq]
    rw [genericResultant_eval]
    exact hres
  have hmono : volume {x : Fin (d * d) → ℝ |
      ∃ t : ℝ, 1 < ((matrixFromCoords d x).charpoly).rootMultiplicity t}
      ≤ volume {x : Fin (d * d) → ℝ | MvPolynomial.eval x (genericResultant d) = 0} :=
    measure_mono hsub
  rw [hnull] at hmono
  exact le_antisymm hmono zero_le

end JinWishart
