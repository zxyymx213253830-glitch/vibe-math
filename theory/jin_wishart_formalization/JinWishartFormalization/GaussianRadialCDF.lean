import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Exponential
import JinWishartFormalization.GaussianRadialLaw
import JinWishartFormalization.RadialIntegration
import JinWishartFormalization.Theorem1Formula

open MeasureTheory Set ProbabilityTheory
open intervalIntegral
open scoped ENNReal

namespace JinWishart

noncomputable def complexGaussianEnergy (z : ℂ) : ℝ := ‖z‖ ^ 2 / 2

@[fun_prop]
theorem measurable_complexGaussianEnergy : Measurable complexGaussianEnergy := by
  unfold complexGaussianEnergy
  fun_prop

private noncomputable def complexGaussianRadialPDF (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2)

private theorem integrable_complexGaussianRadialPDF :
    Integrable (fun z : ℂ ↦ complexGaussianRadialPDF ‖z‖) volume := by
  have h₁ : IntegrableOn (fun r : ℝ ↦ r * complexGaussianRadialPDF r) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (s := (1 : ℝ)) (by norm_num) (by norm_num)
    have h' := h.const_mul ((2 * Real.pi)⁻¹)
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 h'
    intro r hr
    simp only [complexGaussianRadialPDF]
    rw [show -(r ^ 2) / 2 = -(1 / 2) * r ^ 2 by ring]
    rw [Real.rpow_one]
    ring
  exact (integrable_fun_norm_addHaar (μ := (volume : Measure ℂ))
    (f := complexGaussianRadialPDF)).2 (by
      simpa [Complex.finrank_real_complex, complexGaussianRadialPDF,
        pow_one, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h₁)

private theorem integral_radiusGaussian (R : ℝ) (hR : 0 ≤ R) :
    ∫ r in Ioc (0 : ℝ) R, r * complexGaussianRadialPDF r =
      (2 * Real.pi)⁻¹ * (1 - Real.exp (-(R ^ 2) / 2)) := by
  rw [← integral_of_le hR]
  have hderiv : ∀ u ∈ Icc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ ↦ -Real.exp (-(t ^ 2) / 2))
        (u * Real.exp (-(u ^ 2) / 2)) u := by
    intro u hu
    have hinner : HasDerivAt (fun t : ℝ ↦ -(t ^ 2) / 2) (-u) u := by
      convert (((hasDerivAt_id u).pow 2).div_const 2).neg using 1
      · funext t
        simp [Function.comp_def, id]
        ring
      · simp [id]
    convert ((Real.hasDerivAt_exp (-(u ^ 2) / 2)).comp u hinner).neg using 1
    · funext t
      simp [Function.comp_def, id]
    · simp [id]
      ring
  have hint : IntervalIntegrable (fun r : ℝ ↦ r * Real.exp (-(r ^ 2) / 2))
      volume 0 R := by
    exact (show Continuous (fun r : ℝ ↦ r * Real.exp (-(r ^ 2) / 2)) by fun_prop)
      |>.intervalIntegrable 0 R
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (by fun_prop) (fun u hu ↦ hderiv u (Ioo_subset_Icc_self hu)) hint
  have hfun : (fun r : ℝ ↦ r * complexGaussianRadialPDF r) =
      (fun r ↦ (2 * Real.pi)⁻¹ * (r * Real.exp (-(r ^ 2) / 2))) := by
    funext r
    simp [complexGaussianRadialPDF]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, hFTC]
  simp [complexGaussianRadialPDF]
  <;> ring

private theorem integral_complex_radial_closedBall (R : ℝ) (f : ℝ → ℝ) :
    ∫ z in Metric.closedBall (0 : ℂ) R, f ‖z‖ ∂volume =
      2 * Real.pi * ∫ r in Ioc (0 : ℝ) R, r * f r := by
  let g : ℝ → ℝ := (Iic R).indicator f
  have hfun : (fun z : ℂ ↦ g ‖z‖) =
      (Metric.closedBall (0 : ℂ) R).indicator (fun z ↦ f ‖z‖) := by
    funext z
    simp [g, Set.indicator, Metric.closedBall, dist_eq_norm]
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
  rw [← hfun, integral_complex_radial]
  rw [show (fun r : ℝ ↦ r * g r) = (Iic R).indicator (fun r ↦ r * f r) by
    funext r
    by_cases hr : r ≤ R <;> simp [g, hr]]
  rw [MeasureTheory.integral_indicator measurableSet_Iic]
  rw [Measure.restrict_restrict measurableSet_Iic]
  rw [inter_comm]
  rw [show Ioi (0 : ℝ) ∩ Iic R = Ioc 0 R by ext r; simp]

theorem stdGaussian_complex_closedBall (R : ℝ) (hR : 0 ≤ R) :
    (stdGaussian ℂ) (Metric.closedBall (0 : ℂ) R) =
      ENNReal.ofReal (1 - Real.exp (-(R ^ 2) / 2)) := by
  have hballInt :
      ∫ z in Metric.closedBall (0 : ℂ) R, complexGaussianRadialPDF ‖z‖ =
        1 - Real.exp (-(R ^ 2) / 2) := by
    rw [integral_complex_radial_closedBall, integral_radiusGaussian R hR]
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    field_simp [hpi]
  rw [stdGaussian_complex_eq_radialDensity,
    withDensity_apply _ measurableSet_closedBall]
  have hInt : Integrable (fun z : ℂ ↦ complexGaussianRadialPDF ‖z‖)
      (volume.restrict (Metric.closedBall (0 : ℂ) R)) :=
    integrable_complexGaussianRadialPDF.restrict
  have hnonneg : 0 ≤ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) R)]
      (fun z : ℂ ↦ complexGaussianRadialPDF ‖z‖) :=
    ae_of_all _ fun z ↦ by
      unfold complexGaussianRadialPDF
      positivity
  change (∫⁻ z in Metric.closedBall (0 : ℂ) R,
    ENNReal.ofReal (complexGaussianRadialPDF ‖z‖) ∂volume) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
  simpa [complexGaussianRadialPDF] using congrArg ENNReal.ofReal hballInt

/-- Radial PDF of a standard Gaussian in `d` real dimensions. -/
noncomputable def euclideanGaussianRadialPDF (d : ℕ) (r : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-(r ^ 2) / 2)

/-- The standard Gaussian mass of a closed ball in even dimension, reduced to
an explicit one-dimensional radial integral. -/
theorem stdGaussian_euclidean_closedBall {ι : Type*} [Fintype ι]
    [Nontrivial (EuclideanSpace ℝ ι)]
    (k : ℕ) (hk : Module.finrank ℝ (EuclideanSpace ℝ ι) = 2 * k)
    (R : ℝ) (hR : 0 ≤ R) :
    (stdGaussian (EuclideanSpace ℝ ι)) (Metric.closedBall (0 : EuclideanSpace ℝ ι) R) =
      ENNReal.ofReal ((2 * (k : ℝ) * ((Real.pi ^ k) / (Nat.factorial k : ℝ))) *
        ∫ r in Ioc (0 : ℝ) R, r ^ (2 * k - 1) * euclideanGaussianRadialPDF
          (Fintype.card ι) r) := by
  let f : EuclideanSpace ℝ ι → ℝ := fun z ↦ euclideanGaussianRadialPDF
    (Fintype.card ι) ‖z‖
  have hcont : Continuous f := by
    change Continuous (fun z : EuclideanSpace ℝ ι ↦
      euclideanGaussianRadialPDF (Fintype.card ι) ‖z‖)
    fun_prop [euclideanGaussianRadialPDF]
  have hInt : Integrable f (volume.restrict
      (Metric.closedBall (0 : EuclideanSpace ℝ ι) R)) := by
    exact hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ ι) R)
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (Metric.closedBall (0 : EuclideanSpace ℝ ι) R)] f :=
    ae_of_all _ fun z ↦ by
      change 0 ≤ euclideanGaussianRadialPDF (Fintype.card ι) ‖z‖
      unfold euclideanGaussianRadialPDF
      positivity
  have hballInt :
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) R, f z ∂volume =
        (2 * (k : ℝ) * ((Real.pi ^ k) / (Nat.factorial k : ℝ))) *
          ∫ r in Ioc (0 : ℝ) R, r ^ (2 * k - 1) * euclideanGaussianRadialPDF
            (Fintype.card ι) r := by
    change (∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) R,
      euclideanGaussianRadialPDF (Fintype.card ι) ‖z‖ ∂volume) = _
    rw [integral_radial_even_dim_closedBall k hk R hR]
  rw [stdGaussian_euclidean_eq_radialDensity,
    withDensity_apply _ measurableSet_closedBall]
  change (∫⁻ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) R,
      ENNReal.ofReal (f z) ∂volume) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg, hballInt]

/-- Squared Gaussian energy on a Euclidean space. -/
noncomputable def euclideanGaussianEnergy {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℝ ι) : ℝ := ‖z‖ ^ 2 / 2

@[fun_prop]
theorem measurable_euclideanGaussianEnergy {ι : Type*} [Fintype ι] :
    Measurable (euclideanGaussianEnergy (ι := ι)) := by
  unfold euclideanGaussianEnergy
  fun_prop

/-- The energy sublevel event in an even-dimensional standard Gaussian space is
exactly a centered closed ball; its probability is therefore the radial integral
from `stdGaussian_euclidean_closedBall`. -/
theorem stdGaussian_euclideanEnergy_measure_Iic {ι : Type*} [Fintype ι]
    [Nontrivial (EuclideanSpace ℝ ι)] (k : ℕ)
    (hk : Module.finrank ℝ (EuclideanSpace ℝ ι) = 2 * k)
    (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (euclideanGaussianEnergy (ι := ι)) (Iic x) =
      ENNReal.ofReal ((2 * (k : ℝ) * ((Real.pi ^ k) / (Nat.factorial k : ℝ))) *
        ∫ r in Ioc (0 : ℝ) (Real.sqrt (2 * x)),
          r ^ (2 * k - 1) * euclideanGaussianRadialPDF (Fintype.card ι) r) := by
  rw [Measure.map_apply measurable_euclideanGaussianEnergy measurableSet_Iic]
  have hevent : euclideanGaussianEnergy (ι := ι) ⁻¹' Iic x =
      Metric.closedBall (0 : EuclideanSpace ℝ ι) (Real.sqrt (2 * x)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, Metric.mem_closedBall,
      dist_zero_right, euclideanGaussianEnergy]
    constructor
    · intro hz
      have hs : Real.sqrt (2 * x) ^ 2 = 2 * x :=
        Real.sq_sqrt (by positivity)
      have hn : ‖z‖ ^ 2 ≤ Real.sqrt (2 * x) ^ 2 := by nlinarith [hz, hs]
      by_contra hnot
      have hlt : Real.sqrt (2 * x) < ‖z‖ := lt_of_not_ge hnot
      have hsum : 0 < ‖z‖ + Real.sqrt (2 * x) := by
        nlinarith [Real.sqrt_nonneg (2 * x)]
      have hprod := mul_pos (sub_pos.mpr hlt) hsum
      nlinarith
    · intro hz
      have hs : Real.sqrt (2 * x) ^ 2 = 2 * x :=
        Real.sq_sqrt (by positivity)
      have hprod := mul_nonneg (sub_nonneg.mpr hz)
        (add_nonneg (norm_nonneg z) (Real.sqrt_nonneg (2 * x)))
      nlinarith
  rw [hevent]
  exact stdGaussian_euclidean_closedBall k hk (Real.sqrt (2 * x))
    (Real.sqrt_nonneg _)

/-- Substituting `u = r²/2` converts the even-dimensional radial Gaussian
integral to the lower incomplete-Gamma integral. -/
theorem radialGaussian_integral_subst (k : ℕ) (hk : 0 < k)
    (x : ℝ) (hx : 0 ≤ x) :
    ∫ r in (0 : ℝ)..Real.sqrt (2 * x),
        r ^ (2 * k - 1) * Real.exp (-(r ^ 2) / 2) =
      2 ^ (k - 1) * ∫ u in (0 : ℝ)..x, u ^ (k - 1) * Real.exp (-u) := by
  let φ : ℝ → ℝ := fun r ↦ r ^ 2 / 2
  let g : ℝ → ℝ := fun u ↦ u ^ (k - 1) * Real.exp (-u)
  let R := Real.sqrt (2 * x)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 2 * x := by
    dsimp [R]
    exact Real.sq_sqrt (by positivity)
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) R,
      HasDerivAt φ r r := by
    intro r hr
    dsimp [φ]
    convert (((hasDerivAt_id r).pow 2).div_const 2) using 1 <;> simp
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := R) (f := φ) (f' := fun r ↦ r) (g := g)
    hderiv (by fun_prop) (by fun_prop)
  have hend : φ R = x := by
    dsimp [φ]
    rw [hR2]
    ring
  have hkernel (r : ℝ) :
      r ^ (2 * k - 1) * Real.exp (-(r ^ 2) / 2) =
        2 ^ (k - 1) * ((g ∘ φ) r * r) := by
    dsimp [g, φ]
    have hk' : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
    rw [hk', pow_succ, div_pow]
    have hpow : (r ^ 2) ^ (k - 1) = r ^ (2 * (k - 1)) := by
      rw [← pow_mul, mul_comm]
    rw [hpow]
    field_simp
    <;> ring
  calc
    _ = ∫ r in (0 : ℝ)..R, 2 ^ (k - 1) * ((g ∘ φ) r * r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hkernel r
    _ = 2 ^ (k - 1) * ∫ r in (0 : ℝ)..R, (g ∘ φ) r * r := by
      rw [intervalIntegral.integral_const_mul]
    _ = 2 ^ (k - 1) * ∫ u in (0 : ℝ)..x, g u := by
      rw [hsub]
      rw [show φ 0 = 0 by simp [φ], hend]
    _ = _ := rfl

/-- The even-dimensional radial volume and Gaussian density constants simplify
to the unit-rate Gamma normalization. -/
theorem radialGaussian_normalization (k : ℕ) (hk : 0 < k) :
    (2 * (k : ℝ) * ((Real.pi ^ k) / (Nat.factorial k : ℝ))) *
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ (2 * k)) * 2 ^ (k - 1) =
      ((Nat.factorial (k - 1) : ℝ))⁻¹ := by
  have hsqrt : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hpow : Real.sqrt (2 * Real.pi) ^ (2 * k) = (2 * Real.pi) ^ k := by
    rw [pow_mul, hsqrt]
  have hfac : Nat.factorial k = k * Nat.factorial (k - 1) := by
    calc
      Nat.factorial k = Nat.factorial ((k - 1) + 1) := by
        rw [Nat.sub_add_cancel hk]
      _ = ((k - 1) + 1) * Nat.factorial (k - 1) := Nat.factorial_succ _
      _ = k * Nat.factorial (k - 1) := by congr 1 <;> omega
  rw [inv_pow, hpow, hfac]
  have hkpos : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hfactpos : (Nat.factorial (k - 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k - 1)
  have hpipos : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have htwo : (2 : ℝ) ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ]
    congr 1
    omega
  field_simp [hkpos, hfactpos, hpipos]
  rw [mul_pow, ← htwo, ← hfac]
  have hfacCast : (Nat.factorial k : ℝ) =
      (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast hfac
  rw [hfacCast]
  push_cast
  ring

/-- The integer-shape Gamma CDF is its normalized lower-Gamma interval
integral. The proof starts from mathlib's density CDF, uses the density's
support on nonnegative reals, and removes the zero endpoint. -/
theorem cdf_gammaMeasure_nat_eq_lowerGamma (k : ℕ) (hk : 0 < k)
    (x : ℝ) (hx : 0 ≤ x) :
    cdf (gammaMeasure (k : ℝ) 1) x =
      ((Nat.factorial (k - 1) : ℝ)⁻¹) *
        ∫ u in (0 : ℝ)..x, u ^ (k - 1) * Real.exp (-u) := by
  have hkcast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hk).symm
  have hpdf (y : ℝ) (hy : 0 ≤ y) :
      gammaPDFReal (k : ℝ) 1 y =
        ((Nat.factorial (k - 1) : ℝ)⁻¹) * y ^ (k - 1) * Real.exp (-y) := by
    have hGamma : Real.Gamma (k : ℝ) = (Nat.factorial (k - 1) : ℝ) := by
      rw [hkcast, Real.Gamma_nat_eq_factorial]
    have hpow : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk]
      norm_num
    rw [gammaPDFReal, if_pos hy, Real.one_rpow, hGamma, hpow, Real.rpow_natCast]
    simp only [one_mul, neg_mul, neg_one_mul]
    field_simp [Nat.factorial_ne_zero]
  have hpdfNonneg : 0 ≤ᵐ[volume] gammaPDFReal (k : ℝ) 1 :=
    ae_of_all _ (fun y ↦ gammaPDFReal_nonneg (by exact_mod_cast hk) (by norm_num) y)
  have hpdfAEMeas : AEStronglyMeasurable (gammaPDFReal (k : ℝ) 1) volume :=
    (measurable_gammaPDFReal (k : ℝ) 1).aestronglyMeasurable
  have hfinite :
      (∫⁻ y, ENNReal.ofReal (gammaPDFReal (k : ℝ) 1 y) ∂volume) ≠ ∞ := by
    rw [show (fun y ↦ ENNReal.ofReal (gammaPDFReal (k : ℝ) 1 y)) =
        gammaPDF (k : ℝ) 1 by rfl,
      lintegral_gammaPDF_eq_one (by exact_mod_cast hk) (by norm_num)]
    norm_num
  have hpdfInt : Integrable (gammaPDFReal (k : ℝ) 1) volume :=
    (lintegral_ofReal_ne_top_iff_integrable hpdfAEMeas hpdfNonneg).mp hfinite
  have hpdfOn (a : ℝ) : IntegrableOn (gammaPDFReal (k : ℝ) 1) (Iic a) volume :=
    hpdfInt.integrableOn
  have hzero : ∫ y in Iic (0 : ℝ), gammaPDFReal (k : ℝ) 1 y = 0 := by
    rw [integral_Iic_eq_integral_Iio]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have hy' : y < 0 := by simpa using hy
    simp [gammaPDFReal, not_le.mpr hy']
  have hsplit := intervalIntegral.integral_Iic_sub_Iic
    (f := gammaPDFReal (k : ℝ) 1) (a := (0 : ℝ)) (b := x) (hpdfOn 0) (hpdfOn x)
  have hinterval :
      ∫ y in (0 : ℝ)..x, gammaPDFReal (k : ℝ) 1 y =
        ((Nat.factorial (k - 1) : ℝ)⁻¹) *
          ∫ y in (0 : ℝ)..x, y ^ (k - 1) * Real.exp (-y) := by
    calc
      _ = ∫ y in (0 : ℝ)..x,
          ((Nat.factorial (k - 1) : ℝ)⁻¹) * y ^ (k - 1) * Real.exp (-y) := by
            apply intervalIntegral.integral_congr
            intro y hy
            apply hpdf
            have hmem : y ∈ Icc (0 : ℝ) x := by
              simpa [uIcc_of_le hx] using hy
            exact hmem.1
      _ = _ := by
            calc
              _ = ∫ y in (0 : ℝ)..x,
                  ((Nat.factorial (k - 1) : ℝ)⁻¹) *
                    (y ^ (k - 1) * Real.exp (-y)) := by
                      apply intervalIntegral.integral_congr
                      intro y hy
                      ring
              _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [cdf_gammaMeasure_eq_integral (by exact_mod_cast hk) (by norm_num) x]
  calc
    ∫ y in Iic x, gammaPDFReal (k : ℝ) 1 y =
        ∫ y in (0 : ℝ)..x, gammaPDFReal (k : ℝ) 1 y := by
          have h := hsplit
          rw [hzero, sub_zero] at h
          exact h
    _ = _ := hinterval

/-- Combining the even-dimensional ball integral, the radial substitution and
its normalization gives the exact integer-shape lower-Gamma CDF formula. -/
theorem stdGaussian_euclideanEnergy_measure_Iic_lowerGamma {ι : Type*} [Fintype ι]
    [Nontrivial (EuclideanSpace ℝ ι)] (k : ℕ)
    (hk : Module.finrank ℝ (EuclideanSpace ℝ ι) = 2 * k) (hk0 : 0 < k)
    (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (euclideanGaussianEnergy (ι := ι)) (Iic x) =
      ENNReal.ofReal (((Nat.factorial (k - 1) : ℝ)⁻¹) *
        ∫ u in (0 : ℝ)..x, u ^ (k - 1) * Real.exp (-u)) := by
  rw [stdGaussian_euclideanEnergy_measure_Iic (ι := ι) k hk x hx]
  apply congrArg ENNReal.ofReal
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := by simp
  have hcard : Fintype.card ι = 2 * k := hfin.symm.trans hk
  have hrad :
      ∫ r in Ioc (0 : ℝ) (Real.sqrt (2 * x)),
        r ^ (2 * k - 1) * euclideanGaussianRadialPDF (Fintype.card ι) r =
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ (2 * k)) *
        (2 ^ (k - 1) * ∫ u in (0 : ℝ)..x,
          u ^ (k - 1) * Real.exp (-u)) := by
    have hpdf (r : ℝ) : euclideanGaussianRadialPDF (Fintype.card ι) r =
        (Real.sqrt (2 * Real.pi))⁻¹ ^ (2 * k) * Real.exp (-(r ^ 2) / 2) := by
      simp [euclideanGaussianRadialPDF, hcard]
    rw [← intervalIntegral.integral_of_le (Real.sqrt_nonneg _)]
    calc
      _ = ∫ r in (0 : ℝ)..Real.sqrt (2 * x),
          (Real.sqrt (2 * Real.pi))⁻¹ ^ (2 * k) *
            (r ^ (2 * k - 1) * Real.exp (-(r ^ 2) / 2)) := by
              apply intervalIntegral.integral_congr
              intro r hr
              change r ^ (2 * k - 1) * euclideanGaussianRadialPDF
                  (Fintype.card ι) r = _
              rw [hpdf r]
              ring
      _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ (2 * k) *
          ∫ r in (0 : ℝ)..Real.sqrt (2 * x),
            r ^ (2 * k - 1) * Real.exp (-(r ^ 2) / 2) := by
              rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [radialGaussian_integral_subst k hk0 x hx]
  calc
    _ = ((2 * (k : ℝ) * ((Real.pi ^ k) / (Nat.factorial k : ℝ))) *
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ (2 * k)) * 2 ^ (k - 1)) *
          ∫ u in (0 : ℝ)..x, u ^ (k - 1) * Real.exp (-u) := by
            rw [hrad]
            ring
    _ = ((Nat.factorial (k - 1) : ℝ))⁻¹ *
        ∫ u in (0 : ℝ)..x, u ^ (k - 1) * Real.exp (-u) := by
          rw [radialGaussian_normalization k hk0]

/-- The squared norm of a standard Gaussian in an even-dimensional Euclidean
space has the integer-shape, unit-rate Gamma law. -/
theorem stdGaussian_euclideanEnergy_map_eq_gammaMeasure {ι : Type*} [Fintype ι]
    [Nontrivial (EuclideanSpace ℝ ι)] (k : ℕ)
    (hk : Module.finrank ℝ (EuclideanSpace ℝ ι) = 2 * k) (hk0 : 0 < k) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (euclideanGaussianEnergy (ι := ι)) =
      gammaMeasure (k : ℝ) 1 := by
  let μ := (stdGaussian (EuclideanSpace ℝ ι)).map (euclideanGaussianEnergy (ι := ι))
  let ν := gammaMeasure (k : ℝ) 1
  haveI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_gammaMeasure (by exact_mod_cast hk0) (by norm_num)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro x
  by_cases hx : 0 ≤ x
  · have hmass := stdGaussian_euclideanEnergy_measure_Iic_lowerGamma
      (ι := ι) k hk hk0 x hx
    apply (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg μ x) (cdf_nonneg ν x)).mp
    calc
      ENNReal.ofReal (cdf μ x) = μ (Iic x) := ofReal_cdf μ x
      _ = ENNReal.ofReal (cdf ν x) := by
        dsimp [μ, ν] at hmass ⊢
        rw [hmass, cdf_gammaMeasure_nat_eq_lowerGamma k hk0 x hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    have hleftMass : μ (Iic x) = 0 := by
      change (stdGaussian (EuclideanSpace ℝ ι)).map
        (euclideanGaussianEnergy (ι := ι)) (Iic x) = 0
      rw [Measure.map_apply measurable_euclideanGaussianEnergy measurableSet_Iic]
      have hpre : euclideanGaussianEnergy (ι := ι) ⁻¹' Iic x = ∅ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false]
        constructor
        · intro hz
          have hnonneg : 0 ≤ euclideanGaussianEnergy (ι := ι) z := by
            unfold euclideanGaussianEnergy
            positivity
          linarith
        · intro hfalse
          exact False.elim hfalse
      rw [hpre]
      simp
    have hleft : cdf μ x = 0 := by
      have h := ofReal_cdf μ x
      rw [hleftMass] at h
      apply (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg μ x) (by norm_num)).mp
      simpa using h
    have hright : cdf ν x = 0 := by
      rw [cdf_gammaMeasure_eq_integral (by exact_mod_cast hk0) (by norm_num) x]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
      have hy' : y < 0 := lt_of_le_of_lt hy hx'
      simp [gammaPDFReal, not_le.mpr hy']
    rw [hleft, hright]

theorem complexGaussianEnergy_measure_Iic (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian ℂ).map complexGaussianEnergy (Iic x) =
      ENNReal.ofReal (1 - Real.exp (-x)) := by
  rw [Measure.map_apply measurable_complexGaussianEnergy measurableSet_Iic]
  have hevent : complexGaussianEnergy ⁻¹' Iic x =
      Metric.closedBall (0 : ℂ) (Real.sqrt (2 * x)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, Metric.mem_closedBall,
      dist_zero_right, complexGaussianEnergy]
    constructor
    · intro hz
      have hs : Real.sqrt (2 * x) ^ 2 = 2 * x :=
        Real.sq_sqrt (by positivity)
      have hn : ‖z‖ ^ 2 ≤ Real.sqrt (2 * x) ^ 2 := by nlinarith [hz, hs]
      by_contra hnot
      have hlt : Real.sqrt (2 * x) < ‖z‖ := lt_of_not_ge hnot
      have hsum : 0 < ‖z‖ + Real.sqrt (2 * x) := by
        nlinarith [Real.sqrt_nonneg (2 * x)]
      have hprod := mul_pos (sub_pos.mpr hlt) hsum
      nlinarith
    · intro hz
      have hs : Real.sqrt (2 * x) ^ 2 = 2 * x :=
        Real.sq_sqrt (by positivity)
      have hprod := mul_nonneg (sub_nonneg.mpr hz)
        (add_nonneg (norm_nonneg z) (Real.sqrt_nonneg (2 * x)))
      nlinarith
  rw [hevent, stdGaussian_complex_closedBall _ (Real.sqrt_nonneg _)]
  have hs : Real.sqrt (2 * x) ^ 2 = 2 * x := Real.sq_sqrt (by positivity)
  rw [hs]
  congr 1
  ring

theorem cdf_complexGaussianEnergy_eq_expMeasure (x : ℝ) :
    cdf ((stdGaussian ℂ).map complexGaussianEnergy) x = cdf (expMeasure 1) x := by
  haveI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  by_cases hx : 0 ≤ x
  · have hmass := complexGaussianEnergy_measure_Iic x hx
    have hformula := cdf_expMeasure_eq (r := 1) (by norm_num) x
    have hnonneg₁ := cdf_nonneg ((stdGaussian ℂ).map complexGaussianEnergy) x
    have hnonneg₂ := cdf_nonneg (expMeasure 1) x
    apply (ENNReal.ofReal_eq_ofReal_iff hnonneg₁ hnonneg₂).mp
    calc
      ENNReal.ofReal (cdf ((stdGaussian ℂ).map complexGaussianEnergy) x) =
          ((stdGaussian ℂ).map complexGaussianEnergy) (Iic x) := ofReal_cdf _ _
      _ = ENNReal.ofReal (1 - Real.exp (-x)) := hmass
      _ = ENNReal.ofReal (cdf (expMeasure 1) x) := by
        rw [hformula]
        simp [hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hpre : complexGaussianEnergy ⁻¹' Iic x = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false]
      constructor
      · intro hz
        have hE : 0 ≤ complexGaussianEnergy z := by
          unfold complexGaussianEnergy
          positivity
        linarith
      · intro hfalse
        exact False.elim hfalse
    have hzero : ((stdGaussian ℂ).map complexGaussianEnergy) (Iic x) = 0 := by
      rw [Measure.map_apply measurable_complexGaussianEnergy measurableSet_Iic, hpre]
      simp
    rw [cdf_eq_real, cdf_expMeasure_eq (r := 1) (by norm_num), if_neg hx]
    simp [measureReal_def, hzero]

/-- The radial energy of a single central complex-Gaussian sample has the
unit-rate exponential law. This is the scalar `1 × 1` Wishart distribution
result, not the matrix-valued density theorem of the paper. -/
theorem centralScalarSampleEnergy_map_eq_expMeasure :
    (stdGaussian (ComplexSample (m := 1) (n := 1))).map centralScalarSampleEnergy =
      expMeasure 1 := by
  rw [centralScalarSampleEnergy_map_eq_radialGaussianEnergy]
  haveI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro x
  exact cdf_complexGaussianEnergy_eq_expMeasure x

/-- Consequently, the least eigenvalue of the `1 × 1` central complex Gram
sample is exponential. -/
theorem centralScalarSmallestEigenvalue_map_eq_expMeasure :
    (stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (by norm_num)) = expMeasure 1 := by
  have hfun :
      complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (by norm_num) = centralScalarSampleEnergy := by
    funext x
    exact centralScalarSampleSmallestEigenvalue_eq_energy x
  rw [hfun, centralScalarSampleEnergy_map_eq_expMeasure]

/-- The actual largest-eigenvalue event of the central `1 × 1` Wishart law is
the exponential sublevel event. This uses the weak CDF event (`≤`), so it does
not rely on exchanging strict and weak probabilities by an unproved
atomlessness claim. -/
theorem centralScalarLargestEigenvalueCdf_eq_expMeasure (x : ℝ) :
    complexNoncentralWishartLargestEigenvalueCdf
        (m := 1) (n := 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) x =
      expMeasure 1 (Iic x) := by
  rw [complexNoncentralWishartLargestEigenvalueCdf, complexNoncentralWishart]
  rw [Measure.map_apply (measurable_shiftedComplexSampleGram (M :=
    (0 : Matrix (Fin 1) (Fin 1) ℂ))) (measurableSet_largestEigenvalueCdfEvent x)]
  have hpre :
      (fun y : ComplexSample (m := 1) (n := 1) ↦
        complexGram (complexSampleMatrix y + (0 : Matrix (Fin 1) (Fin 1) ℂ))) ⁻¹'
          largestEigenvalueCdfEvent x =
        centralScalarSampleEnergy ⁻¹' Iic x := by
    ext y
    let hW := (complexGram_posSemidef (complexSampleMatrix y)).1
    have hidx : smallestEigenvalue₀Index (n := 1) (by norm_num) =
        (⟨0, by norm_num⟩ : Fin (Fintype.card (Fin 1))) := by
      apply Fin.ext
      simp [smallestEigenvalue₀Index]
    have hmin : hW.eigenvalues₀
        (smallestEigenvalue₀Index (n := 1) (by norm_num)) =
        centralScalarSampleEnergy y := by
      simpa [hW, complexNoncentralSampleSmallestEigenvalue, add_zero] using
        centralScalarSampleSmallestEigenvalue_eq_energy y
    have hmax : hW.eigenvalues₀ (⟨0, by norm_num⟩ : Fin (Fintype.card (Fin 1))) =
        centralScalarSampleEnergy y := by
      rw [← hidx]
      exact hmin
    simp only [Set.mem_preimage]
    simp only [add_zero]
    change complexGram (complexSampleMatrix y) ∈ largestEigenvalueCdfEvent x ↔
      centralScalarSampleEnergy y ∈ Iic x
    rw [largestEigenvalueCdfEvent_iff_largest_eigenvalue₀_le
      _ hW (by norm_num) x]
    simp only [add_zero, hmax, Set.mem_preimage, Set.mem_Iic]
  rw [hpre]
  have hfun : centralScalarSampleEnergy =
      complexGaussianEnergy ∘ centralScalarToComplex := by
    funext y
    exact centralScalarEnergy_eq_complexNorm y
  have hmeas : Measurable centralScalarSampleEnergy := by
    rw [hfun]
    exact measurable_complexGaussianEnergy.comp centralScalarToComplex.continuous.measurable
  rw [← Measure.map_apply hmeas measurableSet_Iic,
    centralScalarSampleEnergy_map_eq_expMeasure]

/-- The CDF in the one-sample central scalar specialization of the paper's
formula is now identified with the actual Gaussian sample's weakest eigenvalue
CDF. -/
theorem theorem1CentralScalarOneSample_eq_sampleSmallestEigenvalueCDF
    (x : ℝ) (hx : 0 ≤ x) :
    theorem1CdfCandidate 1 1 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x =
      cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (by norm_num))) x := by
  rw [theorem1CentralScalarOneSample_eq_exponentialCDF x hx,
    centralScalarSmallestEigenvalue_map_eq_expMeasure]

/-- Theorem 2's one-dimensional central specialization reduces to the same
unit-rate exponential CDF. In dimension one, the largest and smallest
eigenvalues coincide. -/
theorem theorem2CentralScalarOneSample_eq_exponentialCDF (x : ℝ) (hx : 0 ≤ x) :
    theorem2CdfCandidate 1 1 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x = cdf (expMeasure 1) x := by
  rw [theorem2CdfCandidate]
  rw [cdf_expMeasure_eq (r := 1) (by norm_num) x]
  simp [theorem2XiMatrix, theorem2XiEntry, theorem1PsiMatrix,
    theorem1PsiEntry, theorem1GammaIndex, upperGammaNat_zero,
    partialGamma_one, hx]
  have hnonneg : 0 ≤ 1 - Real.exp (-x) := by
    have he : Real.exp (-x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    linarith
  rw [show (1 : ℂ) - Complex.exp (-(x : ℂ)) =
      ((1 - Real.exp (-x) : ℝ) : ℂ) by push_cast; simp]
  rw [Complex.norm_of_nonneg hnonneg]

/-- Theorem 2's central scalar formula equals the probability of the actual
largest-eigenvalue weak-CDF event under the `1 × 1` complex Wishart model. -/
theorem theorem2CentralScalarOneSample_eq_largestEigenvalueEvent
    (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal
        (theorem2CdfCandidate 1 1 0 (by omega) (by omega)
          (fun j : Fin 0 => Fin.elim0 j) x) =
      complexNoncentralWishartLargestEigenvalueCdf
        (m := 1) (n := 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) x := by
  haveI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  rw [theorem2CentralScalarOneSample_eq_exponentialCDF x hx]
  calc
    ENNReal.ofReal (cdf (expMeasure 1) x) = expMeasure 1 (Iic x) :=
      ofReal_cdf _ _
    _ = complexNoncentralWishartLargestEigenvalueCdf
        (m := 1) (n := 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) x :=
      (centralScalarLargestEigenvalueCdf_eq_expMeasure x).symm

end JinWishart
