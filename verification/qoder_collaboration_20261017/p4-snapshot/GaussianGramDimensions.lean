import JinWishartFormalization.GaussianGramProjector
import JinWishartFormalization.GaussianRandomSubspaceLaw
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Real dimensions of the Gram column-space projector

Proof bodies by Codex. Qoder / Qwen3.8-Max supplied a bounded P1 comparison
confirming the left-inverse / restriction-of-scalars route; no Qoder proof
body is claimed. Original responses and the failed longer request are kept
in verification/qoder_collaboration_20261017.

Nonsingularity is explicit. The probability interface still assumes a.e.
full rank of the preceding columns; this file does not prove that premise
for a Gaussian matrix and does not establish a general Wishart density.

[需人工审查] Real/complex dimension conventions, variance convention and
skew-product/model correspondence in the inherited probability interface.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem gramColumnMap_leftInverse {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    Function.LeftInverse (((Aᴴ * A)⁻¹ * Aᴴ).toEuclideanLin) A.toEuclideanLin := by
  intro x
  have hmat : ((Aᴴ * A)⁻¹ * Aᴴ) * A = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA]
  have h := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ => B.toEuclideanLin x) hmat
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply, Matrix.toLpLin_one, LinearMap.id_apply] using h

theorem gramColumnMap_injective {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    Function.Injective A.toEuclideanLin :=
  (gramColumnMap_leftInverse A hA).injective

theorem gramColumnSpace_finrank_complex {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    Module.finrank ℂ A.toEuclideanLin.range = n := by
  rw [LinearMap.finrank_range_of_inj (gramColumnMap_injective A hA)]
  exact finrank_euclideanSpace_fin

theorem gramColumnSpace_finrank_real {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    Module.finrank ℝ (A.toEuclideanLin.range.restrictScalars ℝ) = 2 * n := by
  calc
    _ = Module.finrank ℝ A.toEuclideanLin.range :=
      ((Submodule.restrictScalarsEquiv ℝ ℂ (EuclideanSpace ℂ (Fin m))
        A.toEuclideanLin.range).restrictScalars ℝ).finrank_eq
    _ = 2 * Module.finrank ℂ A.toEuclideanLin.range :=
      finrank_real_of_complex _
    _ = 2 * n := by rw [gramColumnSpace_finrank_complex A hA]

theorem totalGramColumnSpaceReal_finrank {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    Module.finrank ℝ (totalGramColumnSpaceReal A) = 2 * n := by
  simpa only [totalGramColumnSpaceReal, ite_eq_left hA] using
    gramColumnSpace_finrank_real A hA

theorem totalGramColumnSpaceReal_orthogonal_finrank {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    Module.finrank ℝ (totalGramColumnSpaceReal A)ᗮ = 2 * (m - n) := by
  have hsum := (totalGramColumnSpaceReal A).finrank_add_finrank_orthogonal
  rw [totalGramColumnSpaceReal_finrank A hA, finrank_real_of_complex,
    finrank_euclideanSpace_fin] at hsum
  omega

/-- Previous abstract rank hypotheses are discharged by the explicit Gram
nonsingularity event. A Gaussian a.e. full-rank proof is still required before
instantiating this with the actual preceding Gaussian columns. -/
theorem stdGaussian_gram_column_energy_law (m n : ℕ)
    (μ : Measure (Matrix (Fin m) (Fin n) ℂ)) [SFinite μ]
    (hn : 0 < n) (hnm : n < m)
    (hfull : ∀ᵐ A ∂μ, IsUnit (Aᴴ * A).det) :
    (μ.prod (stdGaussian (EuclideanSpace ℂ (Fin m)))).map
      (fun p => (p.1, gaussianSplitEnergy (totalGramColumnSpaceReal p.1) p.2)) =
      μ.prod ((gammaMeasure (n : ℝ) 1).prod (gammaMeasure ((m - n : ℕ) : ℝ) 1)) := by
  apply stdGaussian_random_split_energy_law μ totalGramColumnSpaceReal
    (measurable_totalGramColumnSpaceReal_projection m n) n (m - n) hn
    (Nat.sub_pos_of_lt hnm)
  · filter_upwards [hfull] with A hA
    exact totalGramColumnSpaceReal_finrank A hA
  · filter_upwards [hfull] with A hA
    exact totalGramColumnSpaceReal_orthogonal_finrank A hA

end
end JinWishart

#print axioms JinWishart.gramColumnMap_leftInverse
#print axioms JinWishart.gramColumnMap_injective
#print axioms JinWishart.gramColumnSpace_finrank_complex
#print axioms JinWishart.gramColumnSpace_finrank_real
#print axioms JinWishart.totalGramColumnSpaceReal_finrank
#print axioms JinWishart.totalGramColumnSpaceReal_orthogonal_finrank
#print axioms JinWishart.stdGaussian_gram_column_energy_law
