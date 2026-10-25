import JinWishartFormalization.ActualNoncentralLaplaceCharacterization

/-! Codex. Seed2026102510 exact controls precede source.
[需人工审查] Actual properCN1 law, fixed unitary pushforwards and source noncentrality mapping.
Equal mean Gram gives equal matrix law. A unitary orbit gives conjugate matrix
laws; equality of only mean-Gram eigenvalues is NOT asserted to give matrix-law equality. -/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

private theorem correction_trace_meanGram {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ) :
    (M * T * (1 + T)⁻¹ * Mᴴ).trace = ((Mᴴ * M) * T * (1 + T)⁻¹).trace := by
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

theorem complexNoncentralWishart_eq_of_meanGram_eq {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) ℂ) (hGram : Mᴴ * M = Nᴴ * N) :
    complexNoncentralWishart M = complexNoncentralWishart N := by
  have hPSD : ∀ᵐ W ∂complexNoncentralWishart M, W.PosSemidef :=
    (mem_ae_iff_prob_eq_one Matrix.posSemidef_is_closed.measurableSet).mpr
      (complexNoncentralWishart_measure_posSemidef M)
  apply noncentralWishart_eq_of_PSD_matrixLaplace N hPSD
  intro T hT
  rw [noncentralWishart_PSD_matrixLaplace M T hT,
    correction_trace_meanGram M T, correction_trace_meanGram N T, hGram]

private theorem gaussianMatrixLaw_gram_map {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (complexGaussianMatrixLaw M).map complexGram = complexNoncentralWishart M := by
  have hg : Measurable (complexGram (m := m) (n := n)) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).measurable
  unfold complexGaussianMatrixLaw complexNoncentralWishart
  rw [Measure.map_map hg (measurable_shiftedComplexSampleMatrix M)]
  rfl

theorem complexNoncentralWishart_right_unitary_conjugation {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    (complexNoncentralWishart M).map (fun W => Uᴴ * W * U) =
      complexNoncentralWishart (M * U) := by
  have hg : Measurable (complexGram (m := m) (n := n)) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).measurable
  have hm : Measurable (fun A : Matrix (Fin m) (Fin n) ℂ => A * U) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hc : Measurable (fun W : Matrix (Fin n) (Fin n) ℂ => Uᴴ * W * U) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  rw [← gaussianMatrixLaw_gram_map M, Measure.map_map hc hg]
  have he : (fun W : Matrix (Fin n) (Fin n) ℂ => Uᴴ * W * U) ∘ complexGram =
      complexGram ∘ (fun A : Matrix (Fin m) (Fin n) ℂ => A * U) := by
    funext A
    change Uᴴ * (Aᴴ * A) * U = (A * U)ᴴ * (A * U)
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [he, ← Measure.map_map hg hm,
    complexGaussianMatrixLaw_right_unitary_mean M U hU, gaussianMatrixLaw_gram_map]

theorem complexNoncentralWishart_meanGram_unitary_transport {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (hGram : Nᴴ * N = Uᴴ * (Mᴴ * M) * U) :
    (complexNoncentralWishart M).map (fun W => Uᴴ * W * U) = complexNoncentralWishart N := by
  rw [complexNoncentralWishart_right_unitary_conjugation M U hU]
  apply complexNoncentralWishart_eq_of_meanGram_eq
  rw [Matrix.conjTranspose_mul, hGram]
  simp only [Matrix.mul_assoc]

end
end JinWishart
#print axioms JinWishart.complexNoncentralWishart_eq_of_meanGram_eq
#print axioms JinWishart.complexNoncentralWishart_right_unitary_conjugation
#print axioms JinWishart.complexNoncentralWishart_meanGram_unitary_transport
