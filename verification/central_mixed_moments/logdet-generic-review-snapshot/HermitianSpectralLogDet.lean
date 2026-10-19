import JinWishartFormalization.FiniteSpectrumLogDetGrowth
import JinWishartFormalization.WishartProbability

/-! The full spectral log sum is the real logarithm of the matrix determinant.
Codex deterministic spectral algebra; no probability density assumptions. -/
open Matrix
namespace JinWishart
noncomputable section

theorem hermitian_det_one_add_smul_eigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (r : ℝ) :
    (1+(r : ℂ) • A).det = ((∏ i, (1+r*hA.eigenvalues₀ i) : ℝ) : ℂ) := by
  classical
  let U := hA.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have he : 1+(r : ℂ) • A = Unitary.conjStarAlgAut ℂ _ U (1+(r : ℂ) • D) := by
    rw [map_add,map_one,map_smul]
    rw [← hA.spectral_theorem]
  have hu := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  simp only [Matrix.det_mul,Matrix.det_one] at hu
  rw [Unitary.coe_star] at hu
  have hd : (1+(r : ℂ) • D).det = ((∏ i, (1+r*hA.eigenvalues i) : ℝ) : ℂ) := by
    have hdiag : 1+(r : ℂ) • D = diagonal (fun i => ((1+r*hA.eigenvalues i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i=j
      · subst j
        simp [D,Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply]
      · simp [D,Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply,Matrix.one_apply,hij]
    rw [hdiag,Matrix.det_diagonal]
    norm_cast
  rw [he,Unitary.conjStarAlgAut_apply,Matrix.det_mul,Matrix.det_mul]
  calc
    _ = (1+(r : ℂ) • D).det * ((U : Matrix (Fin n) (Fin n) ℂ).det*
        (star (U : Matrix (Fin n) (Fin n) ℂ)).det) := by ring
    _ = (1+(r : ℂ) • D).det := by rw [hu,mul_one]
    _ = _ := by
      rw [hd]
      congr 1
      exact Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
        (fun i => 1+r*hA.eigenvalues₀ i)

theorem gram_real_logdet_eq_spectral {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (hr : 0 ≤ r) :
    Real.log ((1+(r : ℂ) • complexGram X).det.re) =
      finiteSpectrumLogDet (complexGram_posSemidef X).1.eigenvalues₀ r := by
  rw [hermitian_det_one_add_smul_eigenvalues _ (complexGram_posSemidef X).1]
  simp only [Complex.ofReal_re,finiteSpectrumLogDet]
  exact Real.log_prod (fun i _ => (show 0 < 1+r*(complexGram_posSemidef X).1.eigenvalues₀ i by
    have := complexGram_eigenvalues₀_nonneg X i
    positivity).ne')

theorem hermitian_det_eq_prod_ordered {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    A.det = ((∏ i, hA.eigenvalues₀ i : ℝ) : ℂ) := by
  classical
  rw [hA.det_eq_prod_eigenvalues]
  push_cast
  exact Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
    (fun i => (hA.eigenvalues₀ i : ℂ))

theorem hermitian_real_logdet_eq_sum_log {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hpos : ∀ i, 0 < hA.eigenvalues₀ i) :
    Real.log A.det.re = ∑ i, Real.log (hA.eigenvalues₀ i) := by
  rw [hermitian_det_eq_prod_ordered A hA]
  simp only [Complex.ofReal_re]
  exact Real.log_prod (fun i _ => (hpos i).ne')

end
end JinWishart
#print axioms JinWishart.hermitian_det_one_add_smul_eigenvalues
#print axioms JinWishart.gram_real_logdet_eq_spectral
#print axioms JinWishart.hermitian_det_eq_prod_ordered
#print axioms JinWishart.hermitian_real_logdet_eq_sum_log
