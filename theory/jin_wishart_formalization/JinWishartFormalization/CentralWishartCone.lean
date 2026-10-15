import JinWishartFormalization.TwoRowHermitianThreshold
import JinWishartFormalization.DeepSeekScale20261015.CentralTrace

/-!
# Dimension-independent deterministic assets for the central cone route

These are spectral and kernel identities, not a general Wishart density or
probability theorem. The actual Gaussian-to-Hermitian density is still missing.
In particular, no Lebesgue integral over all complex matrices is introduced.
[需人工审查] Hermitian coordinate volume and eventual paper-model interpretation.
-/

open Matrix Unitary
open scoped ComplexOrder

namespace JinWishart
noncomputable section

/-- Strict matrix threshold in arbitrary dimension, without a spectral density. -/
theorem hermitian_shift_posDef_iff_all_eigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (x : ℝ) :
    (A - (x : ℂ) • 1).PosDef ↔ ∀ i, x < hA.eigenvalues i := by
  have he :
      conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (diagonal (fun i => (hA.eigenvalues i : ℂ) - (x : ℂ))) =
        A - (x : ℂ) • 1 := by
    calc
      _ = conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (diagonal (fun i => (hA.eigenvalues i : ℂ)) - (x : ℂ) • 1) := by
            rw [smul_one_eq_diagonal, diagonal_sub]
      _ = A - (x : ℂ) • 1 := by
            rw [map_sub, map_smul, map_one]
            congr 1
            simpa only [Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
              using hA.spectral_theorem.symm
  rw [← he, conjStarAlgAut_apply, isUnit_coe.posDef_star_right_conjugate_iff,
    posDef_diagonal_iff]
  simp only [← Complex.ofReal_sub, Complex.zero_lt_real, sub_pos]

/-- The strict threshold is the least descending eigenvalue in any nonempty size. -/
theorem hermitian_shift_posDef_iff_smallest {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hn : 0 < n) (x : ℝ) :
    (A - (x : ℂ) • 1).PosDef ↔
      x < hA.eigenvalues₀ (smallestEigenvalue₀Index hn) := by
  rw [hermitian_shift_posDef_iff_all_eigenvalues A hA x]
  have hreindex : (∀ i, x < hA.eigenvalues i) ↔ ∀ i, x < hA.eigenvalues₀ i := by
    let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
      Fintype.equivOfCardEq (Fintype.card_fin _)
    change (∀ i, x < hA.eigenvalues₀ (e.symm i)) ↔ ∀ i, x < hA.eigenvalues₀ i
    constructor
    · intro h i
      simpa using h (e i)
    · intro h i
      exact h (e.symm i)
  rw [hreindex]
  constructor
  · intro h
    exact h _
  · intro h i
    have hmax : i ≤ smallestEigenvalue₀Index hn := by
      apply Fin.le_iff_val_le_val.mpr
      simp [smallestEigenvalue₀Index]
      have hi := i.isLt
      simpa using Nat.le_sub_one_of_lt hi
    exact lt_of_lt_of_le h (hA.eigenvalues₀_antitone hmax)

/-- A deterministic kernel; it is deliberately not named an actual density. -/
def centralConeWeight {n : ℕ} (degree : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  A.det.re ^ degree * Real.exp (-A.trace.re)

theorem centralCone_trace_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℝ) :
    (A + (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).trace.re =
      A.trace.re + (n : ℝ) * x := by
  exact deepseek_central_trace_shift n A x

/-- Retains the determinant polynomial when t>s; only the exponential factors. -/
theorem centralConeWeight_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (degree : ℕ) (x : ℝ) :
    centralConeWeight degree (A + (x : ℂ) • 1) =
      Real.exp (-(n : ℝ) * x) * (A + (x : ℂ) • 1).det.re ^ degree *
        Real.exp (-A.trace.re) := by
  unfold centralConeWeight
  rw [centralCone_trace_shift]
  rw [neg_add, Real.exp_add]
  rw [neg_mul]
  ring

/-- The square case has no determinant polynomial. Still not a probability law. -/
theorem centralConeWeight_square_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℝ) :
    centralConeWeight 0 (A + (x : ℂ) • 1) =
      Real.exp (-(n : ℝ) * x) * centralConeWeight 0 A := by
  rw [centralConeWeight_shift]
  simp [centralConeWeight]

end
end JinWishart

#print axioms JinWishart.hermitian_shift_posDef_iff_all_eigenvalues
#print axioms JinWishart.hermitian_shift_posDef_iff_smallest
#print axioms JinWishart.centralCone_trace_shift
#print axioms JinWishart.centralConeWeight_shift
#print axioms JinWishart.centralConeWeight_square_shift
