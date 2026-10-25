import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed

/-! Codex. Seed2026102509 controls precede source.
Entry-sup norm only; no operator/Frobenius norm substitution. -/
open Matrix Finset
open scoped ComplexOrder Matrix.Norms.Elementwise
namespace JinWishart
noncomputable section

theorem psd_entry_norm_le_trace_re {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i j : Fin n) : ‖A i j‖ ≤ A.trace.re := by
  let U : Matrix (Fin n) (Fin n) ℂ := hA.1.eigenvectorUnitary
  let lam : Fin n → ℝ := hA.1.eigenvalues
  have hU (i k : Fin n) : ‖U i k‖ ≤ 1 := by
    simpa only [U, Matrix.IsHermitian.eigenvectorUnitary_apply,
      OrthonormalBasis.norm_eq_one] using
      (PiLp.norm_apply_le (hA.1.eigenvectorBasis k) i)
  have hlam (k : Fin n) : 0 ≤ lam k := hA.eigenvalues_nonneg k
  have hentry : A i j = ∑ k, U i k * (lam k : ℂ) * star (U j k) := by
    conv_lhs => rw [hA.1.spectral_theorem]
    change ((U * diagonal (fun k => (lam k : ℂ))) * Uᴴ) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have htrace : A.trace.re = ∑ k, lam k := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simp [lam]
  rw [hentry, htrace]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  calc
    ‖U i k * (lam k : ℂ) * star (U j k)‖ = ‖U i k‖ * lam k * ‖U j k‖ := by
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hlam k)]
    _ ≤ 1 * lam k * 1 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hU i k) (hlam k))
        (hU j k) (norm_nonneg _) (mul_nonneg zero_le_one (hlam k))
    _ = lam k := by ring

theorem psd_entrySupNorm_le_trace_re {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) : ‖A‖ ≤ A.trace.re := by
  have ht : 0 ≤ A.trace.re := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simpa using Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      hA.eigenvalues_nonneg i)
  exact (Matrix.norm_le_iff ht).mpr (psd_entry_norm_le_trace_re hA)

end
end JinWishart
#print axioms JinWishart.psd_entry_norm_le_trace_re
#print axioms JinWishart.psd_entrySupNorm_le_trace_re
