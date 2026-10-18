import JinWishartFormalization.CentralWishartClosedDensity
import JinWishartFormalization.GaussianRawCoordinates

/-!
# Actual total received power: central Wishart trace Gamma law

Codex. Reuses the already proved real-Gaussian norm law; no new radial integral.
[需人工审查] Variance-one complex entry convention and trace interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem complexGram_trace_re {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    (complexGram X).trace.re = ∑ i : Fin m, ∑ j : Fin n, ‖X i j‖ ^ 2 := by
  simp only [complexGram, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul,
    Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ((‖X i j‖ : ℂ) ^ 2).re = ‖X i j‖ ^ 2
  norm_cast

theorem complexSampleGram_trace_half_norm {m n : ℕ}
    (z : ComplexSample (m := m) (n := n)) :
    (complexSampleGram z).trace.re = ‖z‖ ^ 2 / 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have h := rawComplexSample_norm_sq_eq_frobenius
    (0 : Matrix (Fin m) (Fin n) ℂ) ((Real.sqrt 2)⁻¹ • z)
  have hz : rawComplexSampleMean (0 : Matrix (Fin m) (Fin n) ℂ) = 0 := by
    ext ij
    simp [rawComplexSampleMean, complexSampleMean]
  rw [hz, sub_zero] at h
  simp only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, Matrix.zero_apply, sub_zero] at h
  change (complexGram (complexSampleMatrix z)).trace.re = _
  rw [complexGram_trace_re, ← h, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs), mul_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Exact Gamma law for total matrix power, including rectangular shapes. -/
theorem complexWishart_trace_law (m n : ℕ) (hmn : 0 < m * n) :
    (complexWishart (m := m) (n := n)).map (fun A => A.trace.re) =
      gammaMeasure ((m * n : ℕ) : ℝ) 1 := by
  rw [complexWishart, Measure.map_map (by fun_prop) measurable_complexSampleGram]
  have he : (fun A : Matrix (Fin n) (Fin n) ℂ => A.trace.re) ∘ complexSampleGram =
      fun z : ComplexSample (m := m) (n := n) => ‖z‖ ^ 2 / 2 := by
    funext z
    exact complexSampleGram_trace_half_norm z
  rw [he]
  exact stdGaussian_half_norm_sq_law (m * n) hmn (by
    simp [ComplexSample, Module.finrank_fintype_fun_eq_card, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm])

end
end JinWishart

#print axioms JinWishart.complexGram_trace_re
#print axioms JinWishart.complexSampleGram_trace_half_norm
#print axioms JinWishart.complexWishart_trace_law
