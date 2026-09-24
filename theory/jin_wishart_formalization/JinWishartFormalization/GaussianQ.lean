import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JinWishartFormalization.MIMOPerformance

/-!
# The scalar Gaussian-Q layer used by the SER formulas

This defines the standard Gaussian tail directly as an improper integral.  It
does not assume a pre-existing `erfc`/`Q` API, and keeps the normalization
proof connected to mathlib's Gaussian integral theorem.
-/

open MeasureTheory Set

namespace JinWishart

/-- Standard normal density on the real line. -/
noncomputable def standardNormalDensity (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- Gaussian Q-function, defined as the standard normal upper-tail integral. -/
noncomputable def gaussianQ (x : ℝ) : ℝ :=
  ∫ t in Ioi x, standardNormalDensity t

/-- Density produced by the square substitution `u = t^2` in the Gaussian tail. -/
noncomputable def gaussianQKernel (u : ℝ) : ℝ :=
  (2 * Real.sqrt u)⁻¹ * standardNormalDensity (Real.sqrt u)

/-- The standard Gaussian has half its mass on the positive half-line. -/
theorem gaussianQ_zero : gaussianQ 0 = 1 / 2 := by
  unfold gaussianQ standardNormalDensity
  rw [integral_const_mul]
  rw [show (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2) / 2)) =
      Real.sqrt (Real.pi / (1 / 2 : ℝ)) / 2 by
        simpa [div_eq_mul_inv, mul_comm] using (integral_gaussian_Ioi (1 / 2 : ℝ))]
  field_simp [Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi)]

/-- Square-substitution representation of the Gaussian tail. The kernel is
`density (sqrt u) / (2 sqrt u)`; its singularity at zero is integrable. -/
theorem gaussianQ_sqrt_eq_transformedTail {x : ℝ} (hx : 0 ≤ x) :
    gaussianQ (Real.sqrt x) = ∫ u in Ioi x, gaussianQKernel u := by
  have hleft : gaussianQ (Real.sqrt x) =
      ∫ t in Ioi (Real.sqrt x), (2 * t) * gaussianQKernel (t ^ 2) := by
    change (∫ t in Ioi (Real.sqrt x), standardNormalDensity t) = _
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg x) ht
    change standardNormalDensity t = (2 * t) * gaussianQKernel (t ^ 2)
    have hroot : Real.sqrt (t ^ 2) = t := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos htpos]
    rw [gaussianQKernel, hroot]
    field_simp [ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) htpos)]
  rw [hleft]
  have hsub := integral_comp_rpow_Ioi_of_pos' (g := gaussianQKernel) (p := 2)
    zero_lt_two (c := x) hx
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at hsub
  simpa [Real.sqrt_eq_rpow, smul_eq_mul] using hsub

/-- The standard Gaussian density is integrable, by the Gaussian integral tail bound. -/
theorem integrable_standardNormalDensity : Integrable standardNormalDensity := by
  have hexp : Integrable (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hform : standardNormalDensity =
      fun t => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    funext t
    unfold standardNormalDensity
    congr 2
    ring
  rw [hform]
  exact hexp.const_mul _

/-- The square-substitution kernel is integrable on the positive half-line.
This supplies the local/tail integrability condition needed by SER layer-cake. -/
theorem integrableOn_gaussianQKernel : IntegrableOn gaussianQKernel (Ioi 0) := by
  have hdensity : IntegrableOn standardNormalDensity (Ioi 0) :=
    integrable_standardNormalDensity.integrableOn
  have hscaled : IntegrableOn
      (fun t : ℝ => t • gaussianQKernel (t ^ (2 : ℝ))) (Ioi 0) := by
    have heq : EqOn (fun t : ℝ => t • gaussianQKernel (t ^ (2 : ℝ)))
        (fun t => (1 / 2 : ℝ) * standardNormalDensity t) (Ioi 0) := by
      intro t ht
      have htpos : 0 < t := ht
      have hroot : Real.sqrt (t ^ (2 : ℝ)) = t := by
        rw [Real.rpow_two, Real.sqrt_sq_eq_abs, abs_of_pos htpos]
      simp only [smul_eq_mul]
      rw [gaussianQKernel, hroot]
      field_simp [ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) htpos)]
    exact (integrableOn_congr_fun heq measurableSet_Ioi).mpr
      (hdensity.const_mul (1 / 2 : ℝ))
  have hcomp : IntegrableOn
      (fun t : ℝ => t ^ ((2 : ℝ) - 1) • gaussianQKernel (t ^ (2 : ℝ))) (Ioi 0) := by
    simpa [show (2 : ℝ) - 1 = 1 by norm_num, smul_eq_mul] using hscaled
  exact (integrableOn_Ioi_comp_rpow_iff' gaussianQKernel
    (p := 2) (by norm_num)).mp hcomp

/-- The transformed Gaussian-Q kernel is nonnegative. -/
theorem gaussianQKernel_nonneg (u : ℝ) : 0 ≤ gaussianQKernel u := by
  unfold gaussianQKernel standardNormalDensity
  positivity

/-- On a nonnegative argument, the Gaussian-Q decrement is the integral of
the square-substitution kernel over the finite interval. -/
theorem gaussianQ_zero_sub_sqrt_eq_interval {x : ℝ} (hx : 0 ≤ x) :
    gaussianQ 0 - gaussianQ (Real.sqrt x) =
      ∫ u in (0 : ℝ)..x, gaussianQKernel u := by
  calc
    gaussianQ 0 - gaussianQ (Real.sqrt x) =
        (∫ u in Ioi (0 : ℝ), gaussianQKernel u) -
          ∫ u in Ioi x, gaussianQKernel u := by
            rw [← gaussianQ_sqrt_eq_transformedTail (x := 0) le_rfl,
              ← gaussianQ_sqrt_eq_transformedTail hx]
            simp
    _ = ∫ u in (0 : ℝ)..x, gaussianQKernel u :=
      intervalIntegral.integral_Ioi_sub_Ioi integrableOn_gaussianQKernel hx

/-- Averaging the Gaussian-Q decrement converts it to a strict-tail integral.
The input statistic need only be nonnegative almost everywhere and measurable;
for a MIMO mode statistic one instantiates `f` with its SNR-scaled eigenvalue. -/
theorem meanGaussianQDecrement_eq_tailIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ)
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf_aemeasurable : AEMeasurable f μ) :
    ∫⁻ ω, ENNReal.ofReal (gaussianQ 0 - gaussianQ (Real.sqrt (f ω))) ∂μ =
      ∫⁻ t in Ioi 0, μ {ω | t < f ω} * ENNReal.ofReal (gaussianQKernel t) := by
  calc
    ∫⁻ ω, ENNReal.ofReal (gaussianQ 0 - gaussianQ (Real.sqrt (f ω))) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..f ω, gaussianQKernel t) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hf_nonneg] with ω hω
          rw [gaussianQ_zero_sub_sqrt_eq_interval hω]
    _ = ∫⁻ t in Ioi 0, μ {ω | t < f ω} * ENNReal.ofReal (gaussianQKernel t) :=
      meanIntegratedKernel_eq_tailIntegral μ f gaussianQKernel hf_nonneg hf_aemeasurable
        (fun t ht =>
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt ht)).2
            (integrableOn_gaussianQKernel.mono_set Ioc_subset_Ioi_self))
        (ae_of_all _ gaussianQKernel_nonneg)

end JinWishart
