import JinWishartFormalization.ActualNoncentralSpectralLaplace
import JinWishartFormalization.GramRankSpectralCoefficient

/-! Codex. Seed2026102507 actual dense-matrix Laplace controls precede source.
Basis-free actual properCN1 noncentral Wishart Laplace transform for PSD T.
The inverse is of I+T, never of possibly singular T.
[需人工审查] Inherited actual measure/model and future density identification. -/
open Matrix MeasureTheory ProbabilityTheory Real Finset
open scoped ComplexOrder
namespace JinWishart
noncomputable section

private theorem gram_diagonal_norm {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    (complexGram B j j).re=∑ i : Fin m,‖B i j‖^2 := by
  simp only [complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re,Complex.star_def,RCLike.norm_sq_eq_def]
  <;> ring

private theorem weighted_gram_trace {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) (w : Fin n → ℝ) :
    ((diagonal (fun j => (w j : ℂ)))*complexGram B).trace.re =
      ∑ a : Fin m × Fin n,‖B a.1 a.2‖^2*w a.2 := by
  calc
    _ = ∑ j : Fin n,w j*(complexGram B j j).re := by
      simp [Matrix.trace,Matrix.diagonal_mul,Complex.mul_re]
    _ = ∑ j : Fin n,w j*(∑ i : Fin m,‖B i j‖^2) := by simp_rw [gram_diagonal_norm]
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem psd_laplace_correction {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.PosSemidef) :
    (M*T*(1+T)⁻¹*Mᴴ).trace.re =
      ∑ a : Fin m × Fin n,
        ‖(M*(hT.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) a.1 a.2‖^2*
          hT.1.eigenvalues a.2/(1+hT.1.eigenvalues a.2) := by
  let U := hT.1.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hT.1.eigenvalues)
  let E : Matrix (Fin n) (Fin n) ℂ := diagonal (fun j => ((1+hT.1.eigenvalues j)⁻¹ : ℝ))
  let F : Matrix (Fin n) (Fin n) ℂ := diagonal (fun j => ((hT.1.eigenvalues j/(1+hT.1.eigenvalues j) : ℝ) : ℂ))
  let P := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) U
  have hn (j : Fin n) : 1+hT.1.eigenvalues j≠0 := by
    have h := hT.eigenvalues_nonneg j
    linarith
  have hd : 1+D=diagonal (fun j => ((1+hT.1.eigenvalues j : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j;simp [D]
    · simp [D,hij]
  have hDE : (1+D)*E=1 := by
    rw [hd,Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      have hz : (1+(hT.1.eigenvalues i : ℂ))≠0 := by exact_mod_cast hn i
      simp [E,hz]
    · simp [E,hij]
  have hP : 1+T=P (1+D) := by
    rw [map_add,map_one,← hT.1.spectral_theorem]
  have hAE : (1+T)*P E=1 := by
    rw [hP,← map_mul,hDE,map_one]
  have hi : (1+T)⁻¹=P E := Matrix.inv_eq_right_inv hAE
  have hDF : D*E=F := by
    dsimp only [D,E,F]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j;simp [div_eq_mul_inv]
    · simp [hij]
  have hTE : T*(1+T)⁻¹=P F := by
    rw [hi,hT.1.spectral_theorem,← map_mul,hDF]
  have hMF : M*P F*Mᴴ=(M*(U : Matrix (Fin n) (Fin n) ℂ))*F*(M*(U : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
    simp only [P,Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [Matrix.mul_assoc M T ((1+T)⁻¹),hTE,hMF,Matrix.trace_mul_cycle,Matrix.trace_mul_comm]
  change (F*complexGram (M*(U : Matrix (Fin n) (Fin n) ℂ))).trace.re=_
  rw [weighted_gram_trace]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [U]
  ring

private theorem psd_laplace_prefactor (m : ℕ) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.PosSemidef) :
    (∏ a : Fin m × Fin n,(1+hT.1.eigenvalues a.2)⁻¹)=(‖(1+T).det‖^m)⁻¹ := by
  have hd : (1+T).det=((∏ j : Fin n,(1+hT.1.eigenvalues j) : ℝ) : ℂ) := by
    have h := hermitian_det_one_add_complex_smul T hT.1 (1 : ℂ)
    simpa only [one_smul,one_mul,Complex.ofReal_prod,Complex.ofReal_add,Complex.ofReal_one] using h
  have hN : ‖(1+T).det‖=∏ j : Fin n,(1+hT.1.eigenvalues j) := by
    rw [hd,Complex.norm_of_nonneg]
    exact Finset.prod_nonneg (fun j _ => by have h := hT.eigenvalues_nonneg j;linarith)
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Finset.prod_inv_distrib,inv_pow,hN]

theorem actualNoncentralPSD_matrixLaplace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.PosSemidef) :
    (∫ z : ComplexSample (m := m) (n := n),
      Real.exp (-(T*complexGram (complexSampleMatrix z+M)).trace.re)
      ∂stdGaussian (ComplexSample (m := m) (n := n))) =
      (‖(1+T).det‖^m)⁻¹*Real.exp (-(M*T*(1+T)⁻¹*Mᴴ).trace.re) := by
  rw [actualNoncentralPSD_integral_exp_spectral M T hT,psd_laplace_prefactor m T hT,
    ← psd_laplace_correction M T hT]

theorem noncentralWishart_PSD_matrixLaplace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.PosSemidef) :
    (∫ W : Matrix (Fin n) (Fin n) ℂ,Real.exp (-(T*W).trace.re) ∂complexNoncentralWishart M) =
      (‖(1+T).det‖^m)⁻¹*Real.exp (-(M*T*(1+T)⁻¹*Mᴴ).trace.re) := by
  have hc : Continuous (fun W : Matrix (Fin n) (Fin n) ℂ => Real.exp (-(T*W).trace.re)) :=
    Real.continuous_exp.comp (Complex.continuous_re.comp
      (continuous_const.matrix_mul continuous_id).matrix_trace).neg
  rw [complexNoncentralWishart,integral_map (measurable_shiftedComplexSampleGram M).aemeasurable hc.measurable.aestronglyMeasurable]
  exact actualNoncentralPSD_matrixLaplace M T hT

end
end JinWishart
#print axioms JinWishart.actualNoncentralPSD_matrixLaplace
#print axioms JinWishart.noncentralWishart_PSD_matrixLaplace
