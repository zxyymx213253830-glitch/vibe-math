import JinWishartFormalization.PSDTraceNormGeometry
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! Codex. Seed2026102509 controls precede source.
A quantitative entry-sup bound, proved using pinned Gershgorin and spectral positivity. -/
open Matrix Finset
open scoped ComplexOrder Matrix.Norms.Elementwise
namespace JinWishart
noncomputable section

theorem hermitian_scalar_shift_posSemidef {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (c : ℝ) (hc : (n : ℝ) * ‖H‖ ≤ c) :
    ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - H).PosSemidef := by
  let B : Matrix (Fin n) (Fin n) ℂ := (c : ℂ) • 1 - H
  have hB : B.IsHermitian := (Matrix.isHermitian_one.smul (by simp [isSelfAdjoint_iff] : IsSelfAdjoint (c : ℂ))).sub hH
  apply hB.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  let lam : ℝ := hB.eigenvalues i
  have hv : Module.End.HasEigenvector (Matrix.toLin' B) (lam : ℂ) ⇑(hB.eigenvectorBasis i) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have hh := hB.mulVec_eigenvectorBasis i
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)] at hh
      convert hh using 1 <;> rfl
    · exact (WithLp.ofLp_eq_zero 2).ne.2 (hB.eigenvectorBasis.orthonormal.ne_zero i)
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (A := B) (μ := (lam : ℂ)) hv.hasUnifEigenvalue
  rw [mem_closedBall_iff_norm'] at hk
  have hdiag : B k k = (c : ℂ) - H k k := by simp [B]
  have hoff : ∑ j ∈ Finset.univ.erase k, ‖B k j‖ =
      ∑ j ∈ Finset.univ.erase k, ‖H k j‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hkj : k ≠ j := (Finset.ne_of_mem_erase hj).symm
    simp [B, Matrix.one_apply_ne hkj]
  rw [hdiag, hoff] at hk
  have hre : c - (H k k).re - lam ≤ ‖(c : ℂ) - H k k - (lam : ℂ)‖ := by
    simpa using Complex.re_le_norm ((c : ℂ) - H k k - (lam : ℂ))
  have hd : (H k k).re ≤ ‖H k k‖ := Complex.re_le_norm _
  have hs : (∑ j ∈ Finset.univ.erase k, ‖H k j‖) + ‖H k k‖ =
      ∑ j, ‖H k j‖ := Finset.sum_erase_add _ _ (Finset.mem_univ k)
  have hall : ∑ j, ‖H k j‖ ≤ (n : ℝ) * ‖H‖ := by
    calc
      ∑ j, ‖H k j‖ ≤ ∑ _j : Fin n, ‖H‖ := Finset.sum_le_sum fun j _ =>
        (norm_le_pi_norm (H k) j).trans (norm_le_pi_norm H k)
      _ = (n : ℝ) * ‖H‖ := by simp
  change 0 ≤ lam
  linarith

end
end JinWishart
#print axioms JinWishart.hermitian_scalar_shift_posSemidef
