import JinWishartFormalization.NuttallQRiceSplit
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Integrability of the order-zero Rice radial kernel

For nonnegative amplitude, the angular representation bounds `I₀(at)` by
`exp(at)`.  Completing the square then gives a Gaussian majorant on the
positive half-line.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

private def riceI0Series (x : ℝ) : ℝ :=
  ∑' n : ℕ, (x ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2)

private theorem riceI0Series_le_exp {x : ℝ} (hx : 0 ≤ x) :
    riceI0Series x ≤ Real.exp x := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hInt :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (x * Real.cos θ)) ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp x := by
    have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hfcont : Continuous (fun θ : ℝ => Real.exp (x * Real.cos θ)) := by
      fun_prop
    have hf : IntervalIntegrable (fun θ : ℝ => Real.exp (x * Real.cos θ))
        volume 0 (2 * Real.pi) := hfcont.intervalIntegrable 0 (2 * Real.pi)
    have hgcont : Continuous (fun _ : ℝ => Real.exp x) := continuous_const
    have hg : IntervalIntegrable (fun _ : ℝ => Real.exp x)
        volume 0 (2 * Real.pi) := hgcont.intervalIntegrable 0 (2 * Real.pi)
    apply intervalIntegral.integral_mono_on (hab := hab) (hf := hf) (hg := hg)
    intro θ hθ
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hx
  rw [angularExpIntegral_eq_factorialSeries] at hInt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hInt
  simp only [sub_zero, mul_one] at hInt
  exact (le_of_mul_le_mul_left hInt hpi).trans_eq (by ring)

private theorem riceRadialKernel_eq_continuousBessel (a t : ℝ) :
    riceRadialKernel a t =
      t * Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
        (modifiedBesselI 0 ((a * t : ℝ) : ℂ)).re := by
  unfold riceRadialKernel
  have h := modifiedBesselI_zero_ofReal_eq_realSeries (a * t)
  have hre := congrArg Complex.re h
  have hseries :
      (∑' n : ℕ, ((a * t) ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) ^ 2)) =
        (modifiedBesselI 0 ((a * t : ℝ) : ℂ)).re := by
    simpa using hre
  rw [hseries]

/-- The Rice radial kernel is integrable on the whole positive half-line for
every nonnegative noncentrality amplitude. -/
theorem riceRadialKernel_integrableOn_Ioi (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (riceRadialKernel a) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun t : ℝ => t * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 / 4 : ℝ)) (s := (1 : ℝ)) (by norm_num) (by norm_num)
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 h
    intro t ht
    change t * Real.exp (-(1 / 4 : ℝ) * t ^ 2) =
      Real.rpow t (1 : ℝ) * Real.exp (-(1 / 4 : ℝ) * t ^ 2)
    exact congrArg (fun z : ℝ => z * Real.exp (-(1 / 4 : ℝ) * t ^ 2))
      (Real.rpow_one t).symm
  have hmajor : IntegrableOn
      (fun t : ℝ => Real.exp (a ^ 2 / 2) *
        (t * Real.exp (-(1 / 4 : ℝ) * t ^ 2))) (Ioi 0) := by
    exact hbase.const_mul (Real.exp (a ^ 2 / 2))
  have hB : Continuous (fun t : ℝ =>
      modifiedBesselI 0 ((a * t : ℝ) : ℂ)) :=
    (continuous_modifiedBesselI 0).comp (by fun_prop)
  have hcont : Continuous (fun t : ℝ =>
      t * Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
        (modifiedBesselI 0 ((a * t : ℝ) : ℂ)).re) := by
    exact (continuous_id.mul
      (Real.continuous_exp.comp (by fun_prop))).mul
        (Complex.continuous_re.comp hB)
  have hmeas : AEStronglyMeasurable (riceRadialKernel a)
      (volume.restrict (Ioi 0)) := by
    apply hcont.measurable.aestronglyMeasurable.congr
    filter_upwards [] with t
    exact (riceRadialKernel_eq_continuousBessel a t).symm
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  have hat : 0 ≤ a * t := mul_nonneg ha ht0
  have hs := riceI0Series_le_exp hat
  have hseries' :
      (∑' n : ℕ, ((a * t) ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2)) ≤
        Real.exp (a * t) := by
    simpa [riceI0Series] using hs
  have hkernel_nonneg : 0 ≤ riceRadialKernel a t := by
    unfold riceRadialKernel
    apply mul_nonneg
    · exact mul_nonneg ht0 (Real.exp_pos _).le
    · exact tsum_nonneg fun n => by positivity
  have hkernelUpper : riceRadialKernel a t ≤
      t * Real.exp (-((t - a) ^ 2 / 2)) := by
    unfold riceRadialKernel
    calc
      _ ≤ t * Real.exp (-((t ^ 2 + a ^ 2) / 2)) * Real.exp (a * t) :=
        mul_le_mul_of_nonneg_left hseries' (by positivity)
      _ = t * (Real.exp (-((t ^ 2 + a ^ 2) / 2)) * Real.exp (a * t)) := by ring
      _ = t * Real.exp (-(t ^ 2 + a ^ 2) / 2 + a * t) := by
        rw [← Real.exp_add]
        congr 2
        rw [neg_div]
      _ = t * Real.exp (-((t - a) ^ 2 / 2)) := by
        congr 2
        field_simp
        ring
  have hpoint :
      ‖riceRadialKernel a t‖ ≤
        ‖Real.exp (a ^ 2 / 2) * (t * Real.exp (-(1 / 4 : ℝ) * t ^ 2))‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hkernel_nonneg,
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ Real.exp (a ^ 2 / 2) * (t * Real.exp (-(1 / 4 : ℝ) * t ^ 2)))]
    have hexp : -(t - a) ^ 2 / 2 ≤ a ^ 2 / 2 - t ^ 2 / 4 := by
      nlinarith [sq_nonneg (t - 2 * a)]
    have hle := Real.exp_le_exp.mpr hexp
    have hrewrite : Real.exp (a ^ 2 / 2) / Real.exp (t ^ 2 / 4) =
        Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    have hle' : Real.exp (-(t - a) ^ 2 / 2) ≤
        Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
      simpa [Real.exp_sub, hrewrite] using hle
    calc
      riceRadialKernel a t ≤ t * Real.exp (-(t - a) ^ 2 / 2) := by
        have hsq : -((t - a) ^ 2 / 2) = -(t - a) ^ 2 / 2 := by ring
        simpa only [hsq] using hkernelUpper
      _ ≤
          t * (Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) :=
        mul_le_mul_of_nonneg_left hle' ht0
      _ = Real.exp (a ^ 2 / 2) *
          (t * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) := by ring
  exact hpoint.trans (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)])

/-- The complex `(p,q) = (1,0)` Nuttall-Q integrand is integrable on the
positive half-line.  This transfers the real Rice-kernel estimate through
`Complex.ofReal` and uses the pointwise factorial-series identity. -/
theorem nuttallQ_10_integrand_integrableOn_Ioi (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (nuttallQIntegrand 1 0 a) (Ioi 0) := by
  have hrice : IntegrableOn (riceRadialKernel a) (Ioi 0) :=
    riceRadialKernel_integrableOn_Ioi a ha
  have hcomplex :
      IntegrableOn (fun t : ℝ => (riceRadialKernel a t : ℂ)) (Ioi 0) :=
    hrice.ofReal
  apply hcomplex.congr
  filter_upwards [] with t
  simp only [nuttallQIntegrand, riceRadialKernel, pow_one]
  rw [← modifiedBesselI_zero_ofReal_eq_realSeries]
  push_cast
  ring

end

end JinWishart
