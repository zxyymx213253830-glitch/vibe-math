import JinWishartFormalization.PSDTraceNormGeometry
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.Normed.Operator.Basic

/-! Codex. Seed2026102509 controls precede source.
Real continuous duals on the full complex matrix space; trace representation
is asserted on Hermitian arguments. All norms here are entry-sup norms. -/
open Matrix Finset
open scoped ComplexOrder Matrix.Norms.Elementwise
namespace JinWishart
noncomputable section

-- Explicit parameters avoid typeclass indexing through the semireducible Matrix alias.
local instance matrixRealDualNorm {n : ℕ} : Norm (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (E := Matrix (Fin n) (Fin n) ℂ) (F := ℝ) (𝕜 := ℝ) (𝕜₂ := ℝ)

private theorem norm_matrix_single {n : ℕ} (i j : Fin n) (z : ℂ) :
    ‖Matrix.single i j z‖ = ‖z‖ := by
  rw [Matrix.single_eq_of_single_single]
  change ‖(Pi.single i (Pi.single j z) : Fin n → Fin n → ℂ)‖ = ‖z‖
  rw [Pi.norm_single, Pi.norm_single]

private theorem dual_single_expand {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) (i j : Fin n) (z : ℂ) :
    L (Matrix.single i j z) = z.re * L (Matrix.single i j 1) +
      z.im * L (Matrix.single i j Complex.I) := by
  have hz : Matrix.single i j z = z.re • Matrix.single i j (1 : ℂ) +
      z.im • Matrix.single i j Complex.I := by
    rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 1
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  rw [hz, map_add, map_smul, map_smul]
  rfl

private def dualTraceKernel {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
      (L (Matrix.single j i 1) : ℂ) - (L (Matrix.single j i Complex.I) : ℂ) * Complex.I

private theorem dual_kernel_trace {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    L W = ((dualTraceKernel L) * W).trace.re := by
  have he : L W = ∑ i, ∑ j, ((W i j).re * L (Matrix.single i j 1) +
      (W i j).im * L (Matrix.single i j Complex.I)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single W]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact dual_single_expand L i j (W i j)
  rw [he]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [dualTraceKernel, Complex.mul_re]
  <;> ring

private theorem dual_kernel_norm {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) : ‖dualTraceKernel L‖ ≤ 2 * ‖L‖ := by
  have hnL : 0 ≤ ‖L‖ := ContinuousLinearMap.opNorm_nonneg (E := Matrix (Fin n) (Fin n) ℂ) (F := ℝ) L
  apply (Matrix.norm_le_iff (mul_nonneg (by norm_num) hnL)).mpr
  intro i j
  have h1 : |L (Matrix.single j i 1)| ≤ ‖L‖ := by
    have hh := ContinuousLinearMap.le_opNorm (E := Matrix (Fin n) (Fin n) ℂ) (F := ℝ) L (Matrix.single j i 1)
    simp only [Real.norm_eq_abs, norm_matrix_single, norm_one, mul_one] at hh
    convert hh using 1 <;> rfl
  have hI : |L (Matrix.single j i Complex.I)| ≤ ‖L‖ := by
    have hh := ContinuousLinearMap.le_opNorm (E := Matrix (Fin n) (Fin n) ℂ) (F := ℝ) L (Matrix.single j i Complex.I)
    simp only [Real.norm_eq_abs, norm_matrix_single, Complex.norm_I, mul_one] at hh
    convert hh using 1 <;> rfl
  change ‖(L (Matrix.single j i 1) : ℂ) - (L (Matrix.single j i Complex.I) : ℂ) * Complex.I‖ ≤ _
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs]
  linarith

theorem exists_hermitian_trace_dual_norm_le {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) :
    ∃ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian ∧
      (∀ W : Matrix (Fin n) (Fin n) ℂ, W.IsHermitian → L W = (H * W).trace.re) ∧
      ‖H‖ ≤ 2 * ‖L‖ := by
  let K := dualTraceKernel L
  let H : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (K + Kᴴ)
  refine ⟨H, ?_, ?_, ?_⟩
  · change Hᴴ = H
    simp [H, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]
  · intro W hW
    have hc : (Kᴴ * W).trace = star (K * W).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hW.eq,
        Matrix.trace_mul_comm]
    have hr : (Kᴴ * W).trace.re = (K * W).trace.re := by
      rw [hc]
      rfl
    rw [dual_kernel_trace]
    change (K * W).trace.re = _
    simp only [H, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
      Matrix.trace_add, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hr]
    ring
  · calc
      ‖H‖ = (1 / 2 : ℝ) * ‖K + Kᴴ‖ := by
        change ‖(1 / 2 : ℝ) • (K + Kᴴ)‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      _ ≤ (1 / 2 : ℝ) * (‖K‖ + ‖Kᴴ‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ = ‖K‖ := by rw [Matrix.norm_conjTranspose]; ring
      _ ≤ 2 * ‖L‖ := dual_kernel_norm L

end
end JinWishart
#print axioms JinWishart.exists_hermitian_trace_dual_norm_le
