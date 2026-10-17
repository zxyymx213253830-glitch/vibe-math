import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Explicit Gram-inverse projector for the random-column-space route

Codex proofs. The formula is total, using the zero-valued nonsingular inverse
on singular Gram matrices. It is an orthogonal column-space projector only
when the Gram determinant is a unit. In particular, full rank is not assumed
silently or inferred from a finite numerical experiment.

[需人工审查] Joint measurability, real/complex coordinate conventions and eventual
Gaussian-model correspondence. Identification with the real orthogonal projection
is proved here; actual Gaussian full-rank exceptions and ranks remain separate.
-/

open MeasureTheory Matrix
namespace JinWishart
noncomputable section

/-- Total inverse is Borel measurable, including its singular branch. -/
theorem measurable_complex_matrix_inverse (n : ℕ) :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul
    continuous_id.matrix_adjugate.measurable

/-- This total formula agrees with the column-space projector at full rank. -/
def gramInverseProjector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ := A * (Aᴴ * A)⁻¹ * Aᴴ

/-- Measurability holds globally, without excluding singular matrices. -/
theorem measurable_gramInverseProjector (m n : ℕ) :
    Measurable (gramInverseProjector (m := m) (n := n)) := by
  have hGram : Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => Aᴴ * A) := by
    fun_prop
  have hInv := (measurable_complex_matrix_inverse n).comp hGram.measurable
  have hAdj : Measurable (fun A : Matrix (Fin m) (Fin n) ℂ => Aᴴ) :=
    continuous_id.matrix_conjTranspose.measurable
  apply Measurable.of_eval_matrix
  intro i j
  simp only [gramInverseProjector, Matrix.mul_apply]
  apply Finset.measurable_sum
  intro a _
  apply Measurable.mul
  · apply Finset.measurable_sum
    intro b _
    exact measurable_id.eval_matrix.mul hInv.eval_matrix
  · exact hAdj.eval_matrix

/-- The explicit projected vector is jointly measurable in preceding columns
and in the fresh vector; no measurable basis selection is needed. -/
theorem measurable_gramInverseProjector_mulVec (m n : ℕ) :
    Measurable (fun p : Matrix (Fin m) (Fin n) ℂ × (Fin m → ℂ) =>
      gramInverseProjector p.1 *ᵥ p.2) := by
  have hProj : Measurable (fun p : Matrix (Fin m) (Fin n) ℂ × (Fin m → ℂ) =>
      gramInverseProjector p.1) :=
    (measurable_gramInverseProjector m n).comp measurable_fst
  apply Measurable.of_eval
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.measurable_sum
  intro j _
  exact hProj.eval_matrix.mul (measurable_snd.eval)

theorem gramInverseProjector_isHermitian {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (gramInverseProjector A).IsHermitian := by
  show (gramInverseProjector A)ᴴ = gramInverseProjector A
  simp only [gramInverseProjector, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

/-- On the full-rank locus the explicit projector fixes each original column. -/
theorem gramInverseProjector_mul_self {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    gramInverseProjector A * A = A := by
  simp only [gramInverseProjector, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]

theorem gramInverseProjector_idempotent {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    gramInverseProjector A * gramInverseProjector A = gramInverseProjector A := by
  change gramInverseProjector A * (A * (Aᴴ * A)⁻¹ * Aᴴ) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, gramInverseProjector_mul_self A hA]
  rfl

theorem gramInverseProjector_normal_equation {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    Aᴴ * gramInverseProjector A = Aᴴ := by
  have h := congrArg Matrix.conjTranspose (gramInverseProjector_mul_self A hA)
  simpa only [Matrix.conjTranspose_mul, (gramInverseProjector_isHermitian A).eq] using h

/-- On the full-rank locus this is precisely the real orthogonal projection,
not merely an abstract idempotent matrix. -/
theorem gramInverseProjector_eq_real_projection {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det)
    (z : EuclideanSpace ℂ (Fin m)) :
    ((A.toEuclideanLin.range).restrictScalars ℝ).starProjection z =
      (gramInverseProjector A).toEuclideanLin z := by
  let K := A.toEuclideanLin.range
  have hmem : (gramInverseProjector A).toEuclideanLin z ∈ K := by
    refine ⟨((Aᴴ * A)⁻¹).toEuclideanLin (Aᴴ.toEuclideanLin z), ?_⟩
    simp only [gramInverseProjector, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  have hres : z - (gramInverseProjector A).toEuclideanLin z ∈ Kᗮ := by
    rw [LinearMap.orthogonal_range]
    change A.toEuclideanLin.adjoint (z - (gramInverseProjector A).toEuclideanLin z) = 0
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, map_sub]
    apply sub_eq_zero.mpr
    have h := congrArg (fun B : Matrix (Fin n) (Fin m) ℂ => B.toEuclideanLin z)
      (gramInverseProjector_normal_equation A hA)
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply] using h.symm
  apply (K.restrictScalars ℝ).eq_starProjection_of_mem_orthogonal hmem
  rw [Submodule.mem_orthogonal]
  intro u hu
  have h := (K.mem_orthogonal _).mp hres u hu
  simpa only [PiLp.inner_apply, RCLike.inner_apply, Complex.inner,
    Complex.re_sum, Complex.zero_re]
    using congrArg Complex.re h

/-- Use zero on the exceptional singular set. Agreement with the actual
column space is asserted only on the full-rank locus, rather than silently
identifying the two spaces at singular matrices. -/
def totalGramColumnSpaceReal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Submodule ℝ (EuclideanSpace ℂ (Fin m)) := by
  classical
  exact if IsUnit (Aᴴ * A).det then A.toEuclideanLin.range.restrictScalars ℝ else ⊥

theorem totalGramColumnSpaceReal_projection {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin m)) :
    (totalGramColumnSpaceReal A).starProjection z =
      (gramInverseProjector A).toEuclideanLin z := by
  by_cases hA : IsUnit (Aᴴ * A).det
  · simpa only [totalGramColumnSpaceReal, ite_eq_left hA] using
      gramInverseProjector_eq_real_projection A hA z
  · have hzero : gramInverseProjector A = 0 := by
      simp only [gramInverseProjector, Matrix.nonsing_inv_apply_not_isUnit _ hA,
        Matrix.mul_zero, Matrix.zero_mul]
    rw [totalGramColumnSpaceReal, ite_eq_right hA, hzero]
    simp

theorem measurable_gramInverseProjector_euclidean (m n : ℕ) :
    Measurable (fun p : Matrix (Fin m) (Fin n) ℂ × EuclideanSpace ℂ (Fin m) =>
      (gramInverseProjector p.1).toEuclideanLin p.2) := by
  change Measurable (fun p : Matrix (Fin m) (Fin n) ℂ × EuclideanSpace ℂ (Fin m) =>
    WithLp.toLp 2 (gramInverseProjector p.1 *ᵥ WithLp.ofLp p.2))
  have hOf : Measurable (WithLp.ofLp : EuclideanSpace ℂ (Fin m) → (Fin m → ℂ)) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℂ)).measurable
  have hTo : Measurable (WithLp.toLp 2 : (Fin m → ℂ) → EuclideanSpace ℂ (Fin m)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℂ)).measurable
  have hInput : Measurable
      (fun p : Matrix (Fin m) (Fin n) ℂ × EuclideanSpace ℂ (Fin m) =>
        (p.1, WithLp.ofLp p.2)) :=
    measurable_fst.prodMk (hOf.comp measurable_snd)
  have hMid := (measurable_gramInverseProjector_mulVec m n).comp hInput
  simpa only [Function.comp_def] using hTo.comp hMid

/-- This supplies the exact joint real-projector measurability premise of
GaussianRandomSubspaceLaw. Full-rank probability and ranks are still separate. -/
theorem measurable_totalGramColumnSpaceReal_projection (m n : ℕ) :
    Measurable (fun p : Matrix (Fin m) (Fin n) ℂ × EuclideanSpace ℂ (Fin m) =>
      (totalGramColumnSpaceReal p.1).starProjection p.2) := by
  simp_rw [totalGramColumnSpaceReal_projection]
  exact measurable_gramInverseProjector_euclidean m n

end
end JinWishart

#print axioms JinWishart.measurable_complex_matrix_inverse
#print axioms JinWishart.measurable_gramInverseProjector
#print axioms JinWishart.measurable_gramInverseProjector_mulVec
#print axioms JinWishart.gramInverseProjector_isHermitian
#print axioms JinWishart.gramInverseProjector_mul_self
#print axioms JinWishart.gramInverseProjector_idempotent
#print axioms JinWishart.gramInverseProjector_normal_equation
#print axioms JinWishart.gramInverseProjector_eq_real_projection
#print axioms JinWishart.totalGramColumnSpaceReal_projection
#print axioms JinWishart.measurable_gramInverseProjector_euclidean
#print axioms JinWishart.measurable_totalGramColumnSpaceReal_projection
