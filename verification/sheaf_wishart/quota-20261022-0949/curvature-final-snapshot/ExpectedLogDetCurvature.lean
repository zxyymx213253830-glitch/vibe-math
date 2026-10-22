import JinWishartFormalization.ExpectedLogDetDerivative
import Mathlib.Analysis.Convex.Deriv

/-! Positive-scale curvature under a first-moment hypothesis only.
Codex. [需人工审查] Differentiation under the integral and actual model mapping.
No inverse moments, fullrank or finite measure premise in the scalar theorem. -/
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem nonnegative_resolvent_square_bound (u r x : ℝ) (hu : 0≤u) (hr : 0<r)
    (hx : r/2<x) : (u/(1+x*u))^2 ≤ (2/r)*u := by
  have hx0 : 0<x := by linarith
  have hd : 0<1+x*u := by positivity
  have hq : 0≤u/(1+x*u) := div_nonneg hu hd.le
  have hsmall : u/(1+x*u) ≤ 2/r := by
    apply (div_le_iff₀ hd).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).2
    nlinarith [mul_nonneg (show 0≤2*x-r by linarith) hu]
  have hlarge : u/(1+x*u) ≤ u := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hu (mul_nonneg hx0.le hu)]
  simpa only [pow_two] using mul_le_mul hsmall hlarge hq (by positivity : 0≤2/r)

theorem integral_resolvent_hasDerivAt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α→ℝ) (hm : Measurable f) (hf : Integrable f μ)
    (hn : ∀ᵐ a ∂μ,0≤f a) (r : ℝ) (hr : 0<r) :
    Integrable (fun a => (f a/(1+r*f a))^2) μ ∧
    HasDerivAt (fun x : ℝ => ∫ a,f a/(1+x*f a) ∂μ)
      (-(∫ a,(f a/(1+r*f a))^2 ∂μ)) r := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioi (r/2)) (F := fun x a => f a/(1+x*f a))
    (F' := fun x a => -(f a/(1+x*f a))^2)
    (bound := fun a => (2/r)*f a) (by apply Ioi_mem_nhds; linarith)
    (Filter.Eventually.of_forall (fun x => (hm.div (measurable_const.add (measurable_const.mul hm))).aestronglyMeasurable))
    (integral_log_one_add_mul_hasDerivAt μ f hm hf hn r hr).1
    (((hm.div (measurable_const.add (measurable_const.mul hm))).pow_const 2).neg.aestronglyMeasurable)
    (by
      filter_upwards [hn] with a ha
      intro x hx
      rw [Real.norm_eq_abs,abs_neg,abs_of_nonneg (sq_nonneg _)]
      exact nonnegative_resolvent_square_bound (f a) r x ha hr hx)
    (hf.const_mul (2/r)) (by
      filter_upwards [hn] with a ha
      intro x hx
      have hx0 : 0<x := by change r/2<x at hx; linarith
      have hd : 1+x*f a≠0 := (by positivity : 0<1+x*f a).ne'
      convert (hasDerivAt_const x (f a)).fun_div
        (((hasDerivAt_id x).mul_const (f a)).const_add 1) hd using 1
      · rfl
      · simp only [id_eq,zero_mul,zero_sub,div_pow]
        ring)
  exact ⟨by simpa using h.1.neg,by simpa only [integral_neg] using h.2⟩

theorem actualCorrelated_expected_resolvent_hasDerivAt {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (hr : 0<r) :
    HasDerivAt (fun x : ℝ => ∑ i,∫ z,
      actualCorrelatedEigenvalue B M i z/(1+x*actualCorrelatedEigenvalue B M i z) ∂stdGaussian _)
      (-(∑ i,∫ z,(actualCorrelatedEigenvalue B M i z/(1+r*actualCorrelatedEigenvalue B M i z))^2 ∂stdGaussian _)) r := by
  classical
  have hi (i : Fin (Fintype.card (Fin n))) :=
    (integral_resolvent_hasDerivAt (stdGaussian _) (actualCorrelatedEigenvalue B M i)
      (measurable_actualCorrelatedEigenvalue B M i) (integrable_actualCorrelatedEigenvalue B M i)
      (ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i)) r hr).2
  convert HasDerivAt.sum (u := Finset.univ) (fun i _ => hi i) using 1
  · funext x
    simp only [Finset.sum_apply]
  · simp only [Finset.sum_neg_distrib]

theorem actualCorrelated_expected_logdet_deriv_hasDerivAt {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (hr : 0<r) :
    HasDerivAt (deriv (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _))
      (-(∑ i,∫ z,(actualCorrelatedEigenvalue B M i z/(1+r*actualCorrelatedEigenvalue B M i z))^2 ∂stdGaussian _)) r := by
  have he : deriv (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _) =ᶠ[𝓝 r]
      (fun x : ℝ => ∑ i,∫ z,actualCorrelatedEigenvalue B M i z/(1+x*actualCorrelatedEigenvalue B M i z) ∂stdGaussian _) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (actualCorrelated_expected_logdet_hasDerivAt B M x hx).deriv
  exact (actualCorrelated_expected_resolvent_hasDerivAt B M r hr).congr_of_eventuallyEq he

theorem actualCorrelated_expected_logdet_second_deriv {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (hr : 0<r) :
    (deriv^[2] (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _)) r =
      -(∑ i,∫ z,(actualCorrelatedEigenvalue B M i z/(1+r*actualCorrelatedEigenvalue B M i z))^2 ∂stdGaussian _) := by
  exact (actualCorrelated_expected_logdet_deriv_hasDerivAt B M r hr).deriv

end
end JinWishart
#print axioms JinWishart.nonnegative_resolvent_square_bound
#print axioms JinWishart.integral_resolvent_hasDerivAt
#print axioms JinWishart.actualCorrelated_expected_resolvent_hasDerivAt
#print axioms JinWishart.actualCorrelated_expected_logdet_deriv_hasDerivAt
#print axioms JinWishart.actualCorrelated_expected_logdet_second_deriv
