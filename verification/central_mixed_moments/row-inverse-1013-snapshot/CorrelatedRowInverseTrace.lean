import JinWishartFormalization.CorrelatedNoiselessLogDetOffset
import JinWishartFormalization.HermitianInverseTrace

/-! Actual ROW inverse-trace powers for the fixed noiseless-surjective model.
Codex. Ordinary nonsingular inverse, not column inverse or pseudoinverse.
[需人工审查] Spectrum measurability and integral/physical model correspondence.
-/
open Matrix Module MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def actualCorrelatedRowEigenvalue {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin m))) (z : ComplexSample (m := m) (n := p)) : ℝ :=
  (complexGram_posSemidef (complexSampleMatrix z*B+M)ᴴ).1.eigenvalues₀ i

def actualCorrelatedRowInverseTracePow {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (k : ℕ) (z : ComplexSample (m := m) (n := p)) : ℝ :=
  (((complexGram (complexSampleMatrix z*B+M)ᴴ)⁻¹)^k).trace.re

set_option maxHeartbeats 1000000 in
theorem measurable_actualCorrelatedRowEigenvalue {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin m))) : Measurable (actualCorrelatedRowEigenvalue B M i) := by
  have hX : Continuous (fun z : ComplexSample (m := m) (n := p) => complexSampleMatrix z*B+M) := by
    apply continuous_matrix
    intro i j
    simp only [Matrix.add_apply,Matrix.mul_apply,complexSampleMatrix]
    fun_prop
  have hG : Continuous (fun z : ComplexSample (m := m) (n := p) =>
      complexGram (complexSampleMatrix z*B+M)ᴴ) := by
    simp only [complexGram,Matrix.conjTranspose_conjTranspose]
    fun_prop
  have hH : Measurable (fun z : ComplexSample (m := m) (n := p) =>
      (⟨complexGram (complexSampleMatrix z*B+M)ᴴ,
        (complexGram_posSemidef (complexSampleMatrix z*B+M)ᴴ).1⟩ : HermitianMatrix m)) :=
    hG.measurable.subtype_mk (h := fun z => (complexGram_posSemidef (complexSampleMatrix z*B+M)ᴴ).1)
  change Measurable ((fun A : HermitianMatrix m => hermitianEigenvalueVector A i) ∘
    (fun z : ComplexSample (m := m) (n := p) =>
      (⟨complexGram (complexSampleMatrix z*B+M)ᴴ,
        (complexGram_posSemidef (complexSampleMatrix z*B+M)ᴴ).1⟩ : HermitianMatrix m)))
  exact ((orderedHermitianEigenvalueCoordinatesContinuous m) i).measurable.comp hH

theorem actualCorrelatedRowEigenvalue_uniform_floor {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    ∃ δ : ℝ, 0<δ ∧ ∀ i z, δ≤actualCorrelatedRowEigenvalue B M i z := by
  obtain ⟨δ,hδ,hf⟩ := correlated_rowGram_uniform_floor B M hm hs
  exact ⟨δ,hδ,fun i z => (hf (complexSampleMatrix z)).trans
    (gramSmallestValue_le_orderedEigenvalue _ hm i)⟩

theorem actualCorrelatedRowEigenvalue_inverse_pow_integrable {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m)
    (i : Fin (Fintype.card (Fin m))) (k : ℕ) :
    Integrable (fun z => (actualCorrelatedRowEigenvalue B M i z)⁻¹^k) (stdGaussian _) := by
  obtain ⟨δ,hδ,hf⟩ := actualCorrelatedRowEigenvalue_uniform_floor B M hm hs
  apply (integrable_const (δ⁻¹^k)).mono'
    (((measurable_actualCorrelatedRowEigenvalue B M i).inv).pow_const k).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    have hp := hδ.trans_le (hf i z)
    change |(actualCorrelatedRowEigenvalue B M i z)⁻¹^k|≤δ⁻¹^k
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hp.le) k)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hp.le) (inv_anti₀ hδ (hf i z)) k)

theorem actualCorrelatedRowInverseTracePow_eq_spectral {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m)
    (k : ℕ) (z : ComplexSample (m := m) (n := p)) :
    actualCorrelatedRowInverseTracePow B M k z =
      ∑ i, (actualCorrelatedRowEigenvalue B M i z)⁻¹^k := by
  obtain ⟨δ,hδ,hf⟩ := actualCorrelatedRowEigenvalue_uniform_floor B M hm hs
  exact hermitian_trace_inverse_pow_eq_orderedEigenvalues _ _
    (fun i => (hδ.trans_le (hf i z)).ne') k

theorem integrable_actualCorrelatedRowInverseTracePow {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m)
    (k : ℕ) : Integrable (actualCorrelatedRowInverseTracePow B M k) (stdGaussian _) := by
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    actualCorrelatedRowEigenvalue_inverse_pow_integrable B M hm hs i k)
  exact hi.congr (ae_of_all _ (fun z => (actualCorrelatedRowInverseTracePow_eq_spectral B M hm hs k z).symm))

end
end JinWishart
#print axioms JinWishart.measurable_actualCorrelatedRowEigenvalue
#print axioms JinWishart.actualCorrelatedRowEigenvalue_uniform_floor
#print axioms JinWishart.actualCorrelatedRowEigenvalue_inverse_pow_integrable
#print axioms JinWishart.actualCorrelatedRowInverseTracePow_eq_spectral
#print axioms JinWishart.integrable_actualCorrelatedRowInverseTracePow
