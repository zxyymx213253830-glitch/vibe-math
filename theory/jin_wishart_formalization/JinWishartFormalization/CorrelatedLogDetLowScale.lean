import JinWishartFormalization.CorrelatedGramTraceMoments
import JinWishartFormalization.WeylComplexHermitian
import JinWishartFormalization.HermitianSpectralLogDet
import JinWishartFormalization.HermitianSquaredTrace
import JinWishartFormalization.LogDetLowScaleSecondOrder
import JinWishartFormalization.LogDetLowScale

/-! Actual full-logdet first and second low-scale coefficients for ZB+M.
Codex. Fixed arbitrary rectangular/singular/zero B, all dimensions, natural logs.
No fullrank, inverse moment or channel coding claim.
[需人工审查] Ordered spectrum measurability, domination/limit interchange and model.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

def actualCorrelatedEigenvalue {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) (z : ComplexSample (m := m) (n := p)) : ℝ :=
  (complexGram_posSemidef (complexSampleMatrix z*B+M)).1.eigenvalues₀ i

def actualCorrelatedMatrixLogDet {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (z : ComplexSample (m := m) (n := p)) : ℝ :=
  Real.log ((1+(r : ℂ) • complexGram (complexSampleMatrix z*B+M)).det.re)

set_option maxHeartbeats 1000000 in
theorem measurable_actualCorrelatedEigenvalue {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) : Measurable (actualCorrelatedEigenvalue B M i) := by
  have hX (k : Fin m) (j : Fin n) : Measurable (fun z : ComplexSample (m := m) (n := p) =>
      (complexSampleMatrix z*B+M) k j) := by
    simp only [Matrix.add_apply,Matrix.mul_apply,complexSampleMatrix]
    fun_prop
  have hg : Measurable (fun z : ComplexSample (m := m) (n := p) =>
      complexGram (complexSampleMatrix z*B+M)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply]
    apply Finset.measurable_sum
    intro k _
    simpa only [RCLike.star_def,Function.comp_apply,Pi.mul_apply] using!
      (Complex.continuous_conj.measurable.comp (hX k i)).mul (hX k j)
  have hH : Measurable (fun z : ComplexSample (m := m) (n := p) =>
      (⟨complexGram (complexSampleMatrix z*B+M),
        (complexGram_posSemidef (complexSampleMatrix z*B+M)).1⟩ : HermitianMatrix n)) :=
    hg.subtype_mk (h := fun z => (complexGram_posSemidef (complexSampleMatrix z*B+M)).1)
  change Measurable ((fun A : HermitianMatrix n => hermitianEigenvalueVector A i) ∘
    (fun z : ComplexSample (m := m) (n := p) =>
      (⟨complexGram (complexSampleMatrix z*B+M),
        (complexGram_posSemidef (complexSampleMatrix z*B+M)).1⟩ : HermitianMatrix n)))
  exact ((orderedHermitianEigenvalueCoordinatesContinuous n) i).measurable.comp hH

theorem actualCorrelatedEigenvalue_nonneg {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) (z : ComplexSample (m := m) (n := p)) :
    0 ≤ actualCorrelatedEigenvalue B M i z := complexGram_eigenvalues₀_nonneg _ i

theorem sum_actualCorrelatedEigenvalues_eq_trace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := p)) :
    (∑ i, actualCorrelatedEigenvalue B M i z) =
      (complexGram (complexSampleMatrix z*B+M)).trace.re := by
  classical
  let h := (complexGram_posSemidef (complexSampleMatrix z*B+M)).1
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hs : (∑ j, h.eigenvalues₀ j) = ∑ j, h.eigenvalues j := by
    simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun j => h.eigenvalues j))
  have ht := congrArg Complex.re h.trace_eq_sum_eigenvalues
  simp only [Complex.re_sum] at ht
  change (complexGram (complexSampleMatrix z*B+M)).trace.re = ∑ j, h.eigenvalues j at ht
  exact hs.trans ht.symm

theorem actualCorrelatedEigenvalue_le_trace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) (z : ComplexSample (m := m) (n := p)) :
    actualCorrelatedEigenvalue B M i z ≤ (complexGram (complexSampleMatrix z*B+M)).trace.re := by
  rw [← sum_actualCorrelatedEigenvalues_eq_trace B M z]
  exact Finset.single_le_sum (fun j _ => actualCorrelatedEigenvalue_nonneg B M j z) (Finset.mem_univ i)

theorem integrable_actualCorrelatedEigenvalue {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) : Integrable (actualCorrelatedEigenvalue B M i) (stdGaussian _) := by
  apply (integrable_actualCorrelatedGram_trace B M).mono'
    (measurable_actualCorrelatedEigenvalue B M i).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (actualCorrelatedEigenvalue_nonneg B M i z)]
    exact actualCorrelatedEigenvalue_le_trace B M i z)

theorem integrable_actualCorrelatedEigenvalue_sq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) :
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)^2) (stdGaussian _) := by
  apply (integrable_actualCorrelatedGram_trace_sq B M).mono'
    ((measurable_actualCorrelatedEigenvalue B M i).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (actualCorrelatedEigenvalue_nonneg B M i z)
      (actualCorrelatedEigenvalue_le_trace B M i z) 2)

theorem actualCorrelatedMatrixLogDet_eq_spectral {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (hr : 0 ≤ r) (z : ComplexSample (m := m) (n := p)) :
    actualCorrelatedMatrixLogDet B M r z =
      finiteSpectrumLogDet (fun i => actualCorrelatedEigenvalue B M i z) r :=
  gram_real_logdet_eq_spectral (complexSampleMatrix z*B+M) r hr

theorem integrable_actualCorrelatedMatrixLogDet {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 ≤ r) :
    Integrable (actualCorrelatedMatrixLogDet B M r) (stdGaussian _) := by
  have he : actualCorrelatedMatrixLogDet B M r =
      fun z => finiteSpectrumLogDet (fun i => actualCorrelatedEigenvalue B M i z) r :=
    funext (actualCorrelatedMatrixLogDet_eq_spectral B M r hr)
  rw [he]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_log_one_add_mul _ _ (integrable_actualCorrelatedEigenvalue B M i)
      (ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i)) r hr)

theorem sum_integral_actualCorrelatedEigenvalues_closed {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    (∑ i, ∫ z, actualCorrelatedEigenvalue B M i z ∂stdGaussian _) =
      ((m : ℂ) • complexGram B+complexGram M).trace.re := by
  rw [← integral_finsetSum _ (fun i _ => integrable_actualCorrelatedEigenvalue B M i)]
  simp_rw [sum_actualCorrelatedEigenvalues_eq_trace]
  exact integral_actualCorrelatedGram_trace B M

theorem sum_integral_actualCorrelatedEigenvalue_sq_closed {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    (∑ i, ∫ z, (actualCorrelatedEigenvalue B M i z)^2 ∂stdGaussian _) =
      (((m : ℂ) • complexGram B+complexGram M)^2).trace.re +
      (m : ℝ)*(complexGram B).trace.re^2+2*(complexGram B).trace.re*(complexGram M).trace.re := by
  rw [← integral_finsetSum _ (fun i _ => integrable_actualCorrelatedEigenvalue_sq B M i)]
  have he (z : ComplexSample (m := m) (n := p)) :
      (∑ i, (actualCorrelatedEigenvalue B M i z)^2) =
      ((complexGram (complexSampleMatrix z*B+M))^2).trace.re :=
    (hermitian_trace_square_eq_orderedEigenvalues _ (complexGram_posSemidef _).1).symm
  simp_rw [he]
  exact integral_actualCorrelatedGram_squaredTrace B M

theorem actualCorrelatedMatrixLogDet_low_scale {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)/r)
      (𝓝[>] 0) (𝓝 ((m : ℂ) • complexGram B+complexGram M).trace.re) := by
  have ht := integral_finiteSpectrumLogDet_low_scale (stdGaussian _) (actualCorrelatedEigenvalue B M)
    (integrable_actualCorrelatedEigenvalue B M)
    (fun i => ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i))
  rw [sum_integral_actualCorrelatedEigenvalues_closed] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  have he : (fun z => finiteSpectrumLogDet (fun i => actualCorrelatedEigenvalue B M i z) r) =
      actualCorrelatedMatrixLogDet B M r :=
    funext (fun z => (actualCorrelatedMatrixLogDet_eq_spectral B M r hr.le z).symm)
  rw [he]

theorem actualCorrelatedMatrixLogDet_low_scale_curvature {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ =>
      (r*((m : ℂ) • complexGram B+complexGram M).trace.re-
        (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _))/r^2)
      (𝓝[>] 0) (𝓝 ((
        (((m : ℂ) • complexGram B+complexGram M)^2).trace.re +
        (m : ℝ)*(complexGram B).trace.re^2+2*(complexGram B).trace.re*(complexGram M).trace.re)/2)) := by
  have ht := integral_finiteSpectrumLogDet_second_order (stdGaussian _) (actualCorrelatedEigenvalue B M)
    (integrable_actualCorrelatedEigenvalue B M) (integrable_actualCorrelatedEigenvalue_sq B M)
    (fun i => ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i))
  rw [sum_integral_actualCorrelatedEigenvalues_closed,sum_integral_actualCorrelatedEigenvalue_sq_closed] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrp : 0 < r := hr
  have he : (fun z => finiteSpectrumLogDet (fun i => actualCorrelatedEigenvalue B M i z) r) =
      actualCorrelatedMatrixLogDet B M r :=
    funext (fun z => (actualCorrelatedMatrixLogDet_eq_spectral B M r hrp.le z).symm)
  rw [he]

end
end JinWishart
#print axioms JinWishart.measurable_actualCorrelatedEigenvalue
#print axioms JinWishart.actualCorrelatedEigenvalue_nonneg
#print axioms JinWishart.sum_actualCorrelatedEigenvalues_eq_trace
#print axioms JinWishart.actualCorrelatedEigenvalue_le_trace
#print axioms JinWishart.integrable_actualCorrelatedEigenvalue
#print axioms JinWishart.integrable_actualCorrelatedEigenvalue_sq
#print axioms JinWishart.actualCorrelatedMatrixLogDet_eq_spectral
#print axioms JinWishart.integrable_actualCorrelatedMatrixLogDet
#print axioms JinWishart.sum_integral_actualCorrelatedEigenvalues_closed
#print axioms JinWishart.sum_integral_actualCorrelatedEigenvalue_sq_closed
#print axioms JinWishart.actualCorrelatedMatrixLogDet_low_scale
#print axioms JinWishart.actualCorrelatedMatrixLogDet_low_scale_curvature
