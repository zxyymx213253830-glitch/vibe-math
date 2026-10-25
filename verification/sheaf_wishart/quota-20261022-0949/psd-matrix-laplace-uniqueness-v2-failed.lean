import JinWishartFormalization.DominatedLocalLaplaceUniqueness
import JinWishartFormalization.HermitianTraceDualGeometry
import JinWishartFormalization.HermitianScalarShiftPSD
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! Codex. Seed2026102509 controls precede source.
[需人工审查] AE PSD support and local exponential tilt specialization.
Equality of ALL PSD matrix tests, not a finite set of directions or moments. -/
open Matrix MeasureTheory ProbabilityTheory Finset
open scoped ComplexOrder Matrix.Norms.Elementwise
namespace JinWishart
noncomputable section
local instance matrixRealDualNorm {n : ℕ} : Norm (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (E := Matrix (Fin n) (Fin n) ℂ) (F := ℝ) (𝕜 := ℝ) (𝕜₂ := ℝ)


theorem finite_PSD_measures_eq_of_matrixLaplace {n : ℕ}
    {μ ν : Measure (Matrix (Fin n) (Fin n) ℂ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ W ∂μ, W.PosSemidef) (hν : ∀ᵐ W ∂ν, W.PosSemidef)
    (hLaplace : ∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef →
      (∫ W, Real.exp (-(T * W).trace.re) ∂μ) =
        ∫ W, Real.exp (-(T * W).trace.re) ∂ν) : μ = ν := by
  let c : ℝ := 2 * n + 1
  let f : Matrix (Fin n) (Fin n) ℂ → ℝ := fun W => c * W.trace.re
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hbound (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.PosSemidef) : ‖W‖ ≤ f W := by
    have ht := psd_entrySupNorm_le_trace_re hW
    have htr : 0 ≤ W.trace.re := (norm_nonneg W).trans ht
    have hc : 1 ≤ c := by dsimp [c]; have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact ht.trans (by dsimp [f]; nlinarith)
  apply eq_of_norm_dominated_localLaplace (E := Matrix (Fin n) (Fin n) ℂ) hf
    (hμ.mono fun W hW => hbound W hW) (hν.mono fun W hW => hbound W hW)
  intro L hL
  obtain ⟨H, hH, hrep, hnorm⟩ := exists_hermitian_trace_dual_norm_le L
  have hl : ‖L‖ < 1 := by convert hL using 1 <;> rfl
  have hnorm' : ‖H‖ ≤ 2 * ‖L‖ := by convert hnorm using 1 <;> rfl
  have hc : (n : ℝ) * ‖H‖ ≤ c := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsmall : ‖H‖ ≤ 2 := by linarith
    have hh := mul_le_mul_of_nonneg_left hsmall hn
    dsimp [c]
    linarith
  let T : Matrix (Fin n) (Fin n) ℂ := (c : ℂ) • 1 - H
  have hT : T.PosSemidef := hermitian_scalar_shift_posSemidef hH c hc
  have hpoint (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.PosSemidef) :
      -f W + L W = -(T * W).trace.re := by
    rw [hrep W hW.1]
    simp only [T, f, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  calc
    (∫ W, Real.exp (-f W + L W) ∂μ) = ∫ W, Real.exp (-(T * W).trace.re) ∂μ :=
      integral_congr_ae (hμ.mono fun W hW => congrArg Real.exp (hpoint W hW))
    _ = ∫ W, Real.exp (-(T * W).trace.re) ∂ν := hLaplace T hT
    _ = ∫ W, Real.exp (-f W + L W) ∂ν :=
      (integral_congr_ae (hν.mono fun W hW => congrArg Real.exp (hpoint W hW))).symm

end
end JinWishart
#print axioms JinWishart.finite_PSD_measures_eq_of_matrixLaplace
