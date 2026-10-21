import JinWishartFormalization.CorrelatedLogDetLowScale
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Positive-scale derivative of actual expected full logdet, without rank hypotheses.
Codex. [需人工审查] Differentiation under integral and physical model correspondence. -/
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem integral_log_one_add_mul_hasDerivAt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hm : Measurable f) (hf : Integrable f μ)
    (hn : ∀ᵐ a ∂μ, 0≤f a) (r : ℝ) (hr : 0<r) :
    Integrable (fun a => f a/(1+r*f a)) μ ∧
    HasDerivAt (fun x : ℝ => ∫ a, Real.log (1+x*f a) ∂μ) (∫ a,f a/(1+r*f a) ∂μ) r := by
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioi (0:ℝ))
    (F := fun x a => Real.log (1+x*f a)) (F' := fun x a => f a/(1+x*f a))
    (bound := f) (Ioi_mem_nhds hr)
  · exact Filter.Eventually.of_forall (fun x => (measurable_const.add (measurable_const.mul hm)).log.aestronglyMeasurable)
  · exact integrable_log_one_add_mul μ f hf hn r hr.le
  · exact (hm.div (measurable_const.add (measurable_const.mul hm))).aestronglyMeasurable
  · filter_upwards [hn] with a ha
    intro x hx
    change 0<x at hx
    have hd : 0<1+x*f a := by positivity
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg ha hd.le)]
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg ha (mul_nonneg hx.le ha)]
  · exact hf
  · filter_upwards [hn] with a ha
    intro x hx
    change 0<x at hx
    have hd : 1+x*f a≠0 := (by positivity : 0<1+x*f a).ne'
    simpa using (((hasDerivAt_id x).mul_const (f a)).const_add 1).log hd

theorem actualCorrelated_expected_logdet_hasDerivAt {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0<r) :
    HasDerivAt (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _)
      (∑ i, ∫ z,actualCorrelatedEigenvalue B M i z/(1+r*actualCorrelatedEigenvalue B M i z) ∂stdGaussian _) r := by
  classical
  have hi (i : Fin (Fintype.card (Fin n))) :=
    (integral_log_one_add_mul_hasDerivAt (stdGaussian _) (actualCorrelatedEigenvalue B M i)
      (measurable_actualCorrelatedEigenvalue B M i) (integrable_actualCorrelatedEigenvalue B M i)
      (ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i)) r hr).2
  have ht := HasDerivAt.sum (u := Finset.univ) (fun i _ => hi i)
  apply ht.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  have he : actualCorrelatedMatrixLogDet B M x =
      fun z => finiteSpectrumLogDet (fun i => actualCorrelatedEigenvalue B M i z) x :=
    funext (actualCorrelatedMatrixLogDet_eq_spectral B M x hx.le)
  rw [he]
  unfold finiteSpectrumLogDet
  rw [integral_finsetSum _ (fun i _ => integrable_log_one_add_mul _ _
    (integrable_actualCorrelatedEigenvalue B M i)
    (ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i)) x hx.le)]
  simp only [Finset.sum_apply]

end
end JinWishart
#print axioms JinWishart.integral_log_one_add_mul_hasDerivAt
#print axioms JinWishart.actualCorrelated_expected_logdet_hasDerivAt
