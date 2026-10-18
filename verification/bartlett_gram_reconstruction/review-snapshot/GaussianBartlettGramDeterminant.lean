import JinWishartFormalization.GaussianBartlettGramRecursion
import JinWishartFormalization.CentralWishartBlockStep

/-!
# Determinant of the generic Bartlett reconstruction

Codex proofs, using the existing dimension-independent block congruence.
The pivot is positive; no inverse, density, or nonsingularity of B is assumed.
[需人工审查] Subsequent probabilistic interpretation and coordinate convention.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def centralBartlettIndexEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl 0) Sum.inr
  left_inv := by
    intro i
    rcases i with i | i
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · rfl
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

def centralBartlettShearCoefficients {n : ℕ} (r : ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin 1) ℂ := fun i _ => star (z i) / (Real.sqrt r : ℂ)

theorem centralBartlettGram_block_factor {n : ℕ} (r : ℝ) (hr : 0 < r)
    (z : EuclideanSpace ℂ (Fin n)) (B : Matrix (Fin n) (Fin n) ℂ) :
    (centralBartlettGram r z B).submatrix (centralBartlettIndexEquiv n)
      (centralBartlettIndexEquiv n) =
      centralBlockStep (Matrix.of (fun _ _ : Fin 1 => (r : ℂ)))
        (centralBartlettShearCoefficients r z) B := by
  have hs : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hr)
  have hsq : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt hr)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [centralBartlettGram, centralBartlettIndexEquiv, centralBlockStep, Matrix.fromBlocks,
      centralBartlettShearCoefficients, Matrix.mul_apply, Matrix.conjTranspose_apply,
      ← hsq] <;> field_simp [hs]

theorem centralBartlettGram_det {n : ℕ} (r : ℝ) (hr : 0 < r)
    (z : EuclideanSpace ℂ (Fin n)) (B : Matrix (Fin n) (Fin n) ℂ) :
    (centralBartlettGram r z B).det = (r : ℂ) * B.det := by
  rw [← Matrix.det_submatrix_equiv_self (centralBartlettIndexEquiv n),
    centralBartlettGram_block_factor r hr]
  rw [centralBlockStep_det, Matrix.det_fin_one]
  rfl

end
end JinWishart

#print axioms JinWishart.centralBartlettGram_block_factor
#print axioms JinWishart.centralBartlettGram_det
