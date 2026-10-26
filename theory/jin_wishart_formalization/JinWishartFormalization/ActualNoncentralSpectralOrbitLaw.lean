import JinWishartFormalization.HermitianSpectralOrbit
import JinWishartFormalization.WeylComplexHermitian

/-! Codex. Seed2026102511 exact controls precede source. Full ordered column-Gram
vector laws, on the original 2mn real Gaussian source. No joint-density claim.
[需人工审查] Borel subtype transport, ordered indices and source noncentrality mapping. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

private def hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : HermitianMatrix n) : HermitianMatrix n :=
  ⟨(U : Matrix (Fin n) (Fin n) ℂ)ᴴ * A.1 * U,
    Matrix.isHermitian_conjTranspose_mul_mul _ A.2⟩

private theorem measurable_hermitianConj {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) : Measurable (hermitianConj U) := by
  exact (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul
    continuous_const).measurable).subtype_mk

private theorem measurable_hermitianSpectrum {n : ℕ} :
    Measurable (hermitianEigenvalueVector (n := n)) :=
  measurable_hermitianEigenvalueVector_of_continuous
    (orderedHermitianEigenvalueCoordinatesContinuous n)

private theorem gramSubtype_map {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    ((stdGaussian (ComplexSample (m := m) (n := n))).map
      (shiftedComplexGramHermitian M)).map Subtype.val = complexNoncentralWishart M := by
  rw [Measure.map_map measurable_subtype_coe (measurable_shiftedComplexGramHermitian M)]
  rfl

private theorem hermitianSubtype_embedding {n : ℕ} :
    MeasurableEmbedding (Subtype.val : HermitianMatrix n → Matrix (Fin n) (Fin n) ℂ) := by
  apply MeasurableEmbedding.subtype_coe
  change MeasurableSet {A : Matrix (Fin n) (Fin n) ℂ | Aᴴ = A}
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet

private theorem gramSubtype_unitary_transport {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ)
    (hGram : Nᴴ * N = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Mᴴ * M) *
      (U : Matrix (Fin n) (Fin n) ℂ)) :
    (((stdGaussian (ComplexSample (m := m) (n := n))).map
      (shiftedComplexGramHermitian M)).map (hermitianConj U)) =
      (stdGaussian (ComplexSample (m := m) (n := n))).map
        (shiftedComplexGramHermitian N) := by
  apply hermitianSubtype_embedding.map_injective
  rw [Measure.map_map measurable_subtype_coe (measurable_hermitianConj U)]
  have hc : Measurable (fun W : Matrix (Fin n) (Fin n) ℂ =>
      (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * W * U) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have he : Subtype.val ∘ hermitianConj U =
      (fun W : Matrix (Fin n) (Fin n) ℂ => (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * W * U) ∘
        (Subtype.val : HermitianMatrix n → Matrix (Fin n) (Fin n) ℂ) := rfl
  rw [he, ← Measure.map_map hc measurable_subtype_coe, gramSubtype_map M,
    gramSubtype_map N]
  exact complexNoncentralWishart_meanGram_unitary_transport M N U
    (by convert Unitary.coe_star_mul_self U using 1 <;> rfl) hGram

theorem actualNoncentral_orderedSpectrum_law_of_meanGram_unitary {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ)
    (hGram : Nᴴ * N = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Mᴴ * M) *
      (U : Matrix (Fin n) (Fin n) ℂ)) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map
      (fun z => fun i => complexNoncentralSampleEigenvalue M i z) =
    (stdGaussian (ComplexSample (m := m) (n := n))).map
      (fun z => fun i => complexNoncentralSampleEigenvalue N i z) := by
  have hi : hermitianEigenvalueVector ∘ hermitianConj U =
      (hermitianEigenvalueVector (n := n)) := by
    funext A
    exact hermitian_eigenvalues₀_unitary_conjugation A.2 U
  have ht := congrArg (fun μ : Measure (HermitianMatrix n) =>
      μ.map hermitianEigenvalueVector) (gramSubtype_unitary_transport M N U hGram)
  rw [Measure.map_map measurable_hermitianSpectrum (measurable_hermitianConj U), hi,
    Measure.map_map measurable_hermitianSpectrum (measurable_shiftedComplexGramHermitian M),
    Measure.map_map measurable_hermitianSpectrum (measurable_shiftedComplexGramHermitian N)] at ht
  exact ht

theorem actualNoncentral_orderedSpectrum_law_of_meanGram_eigenvalues {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) ℂ)
    (h : (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀ =
      (Matrix.isHermitian_conjTranspose_mul_self N).eigenvalues₀) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map
      (fun z => fun i => complexNoncentralSampleEigenvalue M i z) =
    (stdGaussian (ComplexSample (m := m) (n := n))).map
      (fun z => fun i => complexNoncentralSampleEigenvalue N i z) := by
  obtain ⟨U, hU⟩ := exists_unitary_conjugation_of_eigenvalues₀_eq
    (Matrix.isHermitian_conjTranspose_mul_self M)
    (Matrix.isHermitian_conjTranspose_mul_self N) h
  exact actualNoncentral_orderedSpectrum_law_of_meanGram_unitary M N U hU

end
end JinWishart
#print axioms JinWishart.actualNoncentral_orderedSpectrum_law_of_meanGram_unitary
#print axioms JinWishart.actualNoncentral_orderedSpectrum_law_of_meanGram_eigenvalues
