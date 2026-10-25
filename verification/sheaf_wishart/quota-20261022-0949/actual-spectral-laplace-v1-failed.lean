import JinWishartFormalization.ActualDiagonalGramMGF
import JinWishartFormalization.GaussianRectangularFrameLaw
import Mathlib.Analysis.Matrix.PosDef

/-! Codex. Seed2026102507 actual dense properCN1 controls precede source.
General fixed PSD test matrix: actual Laplace transform in its fixed spectral
basis, including singular/zero/empty dimensions. No Wishart joint density.
[需人工审查] Fixed-frame pushforward/Fubini/model and later invariant formula. -/
open Matrix MeasureTheory ProbabilityTheory Real Finset
namespace JinWishart
noncomputable section

private theorem matrixLaw_shift {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)).map (fun A => A+M)=
      complexGaussianMatrixLaw M := by
  unfold complexGaussianMatrixLaw
  rw [Measure.map_map (by fun_prop) (measurable_shiftedComplexSampleMatrix _)]
  congr 1
  funext z
  simp

theorem complexGaussianMatrixLaw_right_unitary_mean {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ*U=1) :
    (complexGaussianMatrixLaw M).map (fun A => A*U)=complexGaussianMatrixLaw (M*U) := by
  rw [← matrixLaw_shift M,Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun A : Matrix (Fin m) (Fin n) ℂ => A*U) ∘ (fun A => A+M)=
      (fun A => A+M*U) ∘ (fun A => A*U) := by
    funext A
    simp [Matrix.add_mul]
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),
    complexGaussianMatrixLaw_right_isometric_projection U hU,matrixLaw_shift]

private theorem trace_psd_spectral {m n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.PosSemidef) (A : Matrix (Fin m) (Fin n) ℂ) :
    (T*complexGram A).trace.re =
      ∑ j : Fin n,hT.1.eigenvalues j*
        (complexGram (A*(hT.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) j j).re := by
  let U : Matrix (Fin n) (Fin n) ℂ := hT.1.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (Complex.ofReal ∘ hT.1.eigenvalues)
  have hs : T=U*D*Uᴴ := by
    simpa [U,D,Unitary.conjStarAlgAut_apply,Unitary.coe_star] using hT.1.spectral_theorem
  have hg : complexGram (A*U)=Uᴴ*complexGram A*U := by
    simp only [complexGram,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have he : (T*complexGram A).trace=(D*complexGram (A*U)).trace := by
    calc
      _ = ((Uᴴ*complexGram A*U)*D).trace := by rw [hs,Matrix.mul_assoc,Matrix.trace_mul_cycle]
      _ = _ := by rw [hg,Matrix.trace_mul_comm]
  rw [he]
  simp [D,U,Matrix.trace,Matrix.diagonal_mul,Complex.mul_re,Function.comp_def]

private theorem diagonalLawIntegral {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (v : Fin n → ℝ) (hv : ∀ j,v j<1) :
    (∫ A : Matrix (Fin m) (Fin n) ℂ,Real.exp (∑ j,v j*(complexGram A j j).re)
      ∂complexGaussianMatrixLaw M) =
      (∏ a : Fin m × Fin n,(1-v a.2)⁻¹)*
        Real.exp (∑ a : Fin m × Fin n,‖M a.1 a.2‖^2*v a.2/(1-v a.2)) := by
  rw [complexGaussianMatrixLaw,integral_map (measurable_shiftedComplexSampleMatrix M) (by unfold complexGram;fun_prop)]
  exact actualNoncentralDiagonalGram_integral_exp M v hv

theorem actualNoncentralPSD_integral_exp_spectral {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.PosSemidef) :
    (∫ z : ComplexSample (m := m) (n := n),
      Real.exp (-(T*complexGram (complexSampleMatrix z+M)).trace.re)
      ∂stdGaussian (ComplexSample (m := m) (n := n))) =
      (∏ a : Fin m × Fin n,(1+hT.1.eigenvalues a.2)⁻¹)*
        Real.exp (-(∑ a : Fin m × Fin n,
          ‖(M*(hT.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) a.1 a.2‖^2*
            hT.1.eigenvalues a.2/(1+hT.1.eigenvalues a.2))) := by
  let U : Matrix (Fin n) (Fin n) ℂ := hT.1.eigenvectorUnitary
  let l : Fin n → ℝ := hT.1.eigenvalues
  have hU : Uᴴ*U=1 := by
    simpa [U,Unitary.coe_star] using Unitary.coe_star_mul_self hT.1.eigenvectorUnitary
  have hv (j : Fin n) : -l j<1 := by
    have h := hT.eigenvalues_nonneg j
    dsimp only [l]
    linarith
  have hsource : (∫ z : ComplexSample (m := m) (n := n),
      Real.exp (-(T*complexGram (complexSampleMatrix z+M)).trace.re)
      ∂stdGaussian (ComplexSample (m := m) (n := n))) =
      ∫ A : Matrix (Fin m) (Fin n) ℂ,Real.exp (-(T*complexGram A).trace.re) ∂complexGaussianMatrixLaw M := by
    rw [complexGaussianMatrixLaw,integral_map (measurable_shiftedComplexSampleMatrix M) (by unfold complexGram;fun_prop)]
  rw [hsource]
  have he (A : Matrix (Fin m) (Fin n) ℂ) : -(T*complexGram A).trace.re=
      ∑ j : Fin n,(-l j)*(complexGram (A*U) j j).re := by
    rw [trace_psd_spectral T hT A]
    simp only [l,U,neg_mul,Finset.sum_neg_distrib]
  simp_rw [he]
  let g : Matrix (Fin m) (Fin n) ℂ → ℝ := fun A => Real.exp (∑ j : Fin n,(-l j)*(complexGram A j j).re)
  change (∫ A : Matrix (Fin m) (Fin n) ℂ,g (A*U) ∂complexGaussianMatrixLaw M)=_
  rw [← integral_map (by fun_prop) (by unfold g complexGram;fun_prop),complexGaussianMatrixLaw_right_unitary_mean M U hU,
    diagonalLawIntegral (M*U) (fun j => -l j) hv]
  simp only [l,U,sub_neg_eq_add,mul_neg,neg_div,Finset.sum_neg_distrib]

theorem actualNoncentralPSD_integrable_exp {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.PosSemidef) :
    Integrable (fun z : ComplexSample (m := m) (n := n) =>
      Real.exp (-(T*complexGram (complexSampleMatrix z+M)).trace.re))
      (stdGaussian (ComplexSample (m := m) (n := n))) := by
  apply Integrable.of_integral_ne_zero
  rw [actualNoncentralPSD_integral_exp_spectral M T hT]
  apply ne_of_gt
  apply mul_pos
  · apply Finset.prod_pos
    intro a _
    exact inv_pos.2 (by have h := hT.eigenvalues_nonneg a.2;linarith)
  · exact Real.exp_pos _

end
end JinWishart
#print axioms JinWishart.complexGaussianMatrixLaw_right_unitary_mean
#print axioms JinWishart.actualNoncentralPSD_integral_exp_spectral
#print axioms JinWishart.actualNoncentralPSD_integrable_exp
