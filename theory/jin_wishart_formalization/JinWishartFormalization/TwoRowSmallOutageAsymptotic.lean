import JinWishartFormalization.Theorem1TwoRowsActualCDF
import JinWishartFormalization.WishartGamma
import JinWishartFormalization.ScalarNoncentralSmallXLimit

/-!
# Hard-edge/outage asymptotic for the actual two-row, one-column model

This module targets the first genuinely four-real-dimensional T4 instance.
The intended normalization is `lambda = ‖complexSampleMean M‖² / 2`, so
the CDF divided by `x²` should tend to `exp (-lambda) / 2`.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped Topology

namespace JinWishart

noncomputable section

private def besselI1QuotientSeries (a r : ℝ) : ℝ :=
  ∑' n : ℕ,
    (((a * r) ^ 2 / 4) ^ n /
      ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))

private def fourDLocalRadialFactor (a r : ℝ) : ℝ :=
  (1 / 2) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
    besselI1QuotientSeries a r

private theorem besselI1RealSeries_eq_mul_quotientSeries (a r : ℝ) :
    besselI1RealSeries (a * r) =
      (a * r / 2) * besselI1QuotientSeries a r := by
  simp [besselI1RealSeries, besselI1QuotientSeries]

private theorem noncentralChiFourRadialKernel_eq_radius_cube_factor
    (a r : ℝ) (ha : a ≠ 0) :
    noncentralChiFourRadialKernel a r = r ^ 3 * fourDLocalRadialFactor a r := by
  rw [noncentralChiFourRadialKernel, besselI1RealSeries_eq_mul_quotientSeries]
  simp only [fourDLocalRadialFactor]
  field_simp [ha]
  <;> ring_nf

private theorem summable_fourDSeriesBound (a : ℝ) :
    Summable (fun n : ℕ => (a ^ 2 / 4) ^ n / (n.factorial : ℝ)) := by
  exact (Real.summable_pow_div_factorial (a ^ 2 / 4)).congr fun n => by
    simp only [Nat.factorial]

private theorem fourDSeriesTerm_bound (a r : ℝ) (hr : r ∈ Icc (-1 : ℝ) 1)
    (n : ℕ) :
    ‖(((a * r) ^ 2 / 4) ^ n /
      ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))‖ ≤
      (a ^ 2 / 4) ^ n / (n.factorial : ℝ) := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
  have hbase : 0 ≤ (a * r) ^ 2 / 4 := by positivity
  have hbase_le : (a * r) ^ 2 / 4 ≤ a ^ 2 / 4 := by nlinarith
  have hpow : ((a * r) ^ 2 / 4) ^ n ≤ (a ^ 2 / 4) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase_le n
  have hfac : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (n + 1)))
  have hden : 0 < (n.factorial : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  calc
    (((a * r) ^ 2 / 4) ^ n /
        ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))
        ≤ ((a * r) ^ 2 / 4) ^ n / (n.factorial : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) hden
          nlinarith
    _ ≤ (a ^ 2 / 4) ^ n / (n.factorial : ℝ) := by
      exact div_le_div_of_nonneg_right hpow hden.le

private theorem continuousOn_besselI1QuotientSeries (a : ℝ) :
    ContinuousOn (besselI1QuotientSeries a) (Icc (-1 : ℝ) 1) := by
  have hsummable := summable_fourDSeriesBound a
  change ContinuousOn (fun r : ℝ => ∑' n : ℕ,
    (((a * r) ^ 2 / 4) ^ n /
      ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))) (Icc (-1 : ℝ) 1)
  apply continuousOn_tsum
  · intro n
    fun_prop
  · exact hsummable
  · intro n r hr
    exact fourDSeriesTerm_bound a r hr n

private theorem continuousAt_besselI1QuotientSeries (a : ℝ) :
    ContinuousAt (besselI1QuotientSeries a) 0 := by
  have hnhds : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Filter.mem_of_superset
      (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
      Ioo_subset_Icc_self
  exact (continuousOn_besselI1QuotientSeries a).continuousAt hnhds

private theorem besselI1QuotientSeries_zero (a : ℝ) :
    besselI1QuotientSeries a 0 = 1 := by
  unfold besselI1QuotientSeries
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

private theorem continuousAt_fourDLocalRadialFactor (a : ℝ) :
    ContinuousAt (fourDLocalRadialFactor a) 0 := by
  have he : ContinuousAt (fun r : ℝ => -((r ^ 2 + a ^ 2) / 2)) 0 := by
    fun_prop
  change ContinuousAt (fun r : ℝ => (1 / 2) *
    Real.exp (-((r ^ 2 + a ^ 2) / 2)) * besselI1QuotientSeries a r) 0
  exact (continuousAt_const.mul
    (Real.continuous_exp.continuousAt.comp he)).mul
      (continuousAt_besselI1QuotientSeries a)

private theorem fourDLocalRadialFactor_zero (a : ℝ) :
    fourDLocalRadialFactor a 0 = (1 / 2) * Real.exp (-(a ^ 2 / 2)) := by
  simp [fourDLocalRadialFactor, besselI1QuotientSeries_zero]

private theorem fourDWeightedAverage_tendsto (a : ℝ) :
    Tendsto (fun R : ℝ => 4 * ∫ s in (0 : ℝ)..1,
      s ^ 3 * fourDLocalRadialFactor a (s * R))
      (𝓝 0) (𝓝 (fourDLocalRadialFactor a 0)) := by
  have hg := continuousAt_fourDLocalRadialFactor a
  have huniform : TendstoUniformlyOn
      (fun R s : ℝ => s ^ 3 * fourDLocalRadialFactor a (s * R))
      (fun s : ℝ => s ^ 3 * fourDLocalRadialFactor a 0)
      (𝓝 0) (Icc (0 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hg ε hε
    filter_upwards [Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun R hR => hR⟩]
      with R hR
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have harg : dist (s * R) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hs0]
      calc
        s * |R| ≤ 1 * |R| := mul_le_mul_of_nonneg_right hs1 (abs_nonneg R)
        _ = |R| := one_mul _
        _ = dist R 0 := by simp [Real.dist_eq]
        _ < δ := hR
    have hdiff := hcont harg
    rw [Real.dist_eq] at hdiff ⊢
    have hfactor : s ^ 3 * fourDLocalRadialFactor a (s * R) -
        s ^ 3 * fourDLocalRadialFactor a 0 =
        s ^ 3 * (fourDLocalRadialFactor a (s * R) -
          fourDLocalRadialFactor a 0) := by ring
    calc
      |s ^ 3 * fourDLocalRadialFactor a 0 -
          s ^ 3 * fourDLocalRadialFactor a (s * R)| =
          s ^ 3 * |fourDLocalRadialFactor a (s * R) -
            fourDLocalRadialFactor a 0| := by
              rw [abs_sub_comm, hfactor, abs_mul,
                abs_of_nonneg (pow_nonneg hs0 3)]
      _ ≤ 1 * |fourDLocalRadialFactor a (s * R) -
            fourDLocalRadialFactor a 0| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              nlinarith [sq_nonneg (s - 1)]
      _ = |fourDLocalRadialFactor a (s * R) -
            fourDLocalRadialFactor a 0| := one_mul _
      _ < ε := hdiff
  have hcont : ∀ᶠ R : ℝ in 𝓝 0,
      ContinuousOn (fun s : ℝ => s ^ 3 * fourDLocalRadialFactor a (s * R))
        (uIcc (0 : ℝ) 1) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with R hR
    have hRabs : |R| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hR.1, hR.2]
    have hfactor : ContinuousOn (fourDLocalRadialFactor a) (Icc (-1 : ℝ) 1) := by
      change ContinuousOn (fun r : ℝ => (1 / 2) *
        Real.exp (-((r ^ 2 + a ^ 2) / 2)) * besselI1QuotientSeries a r)
        (Icc (-1 : ℝ) 1)
      have harg : ContinuousOn (fun r : ℝ => -((r ^ 2 + a ^ 2) / 2))
          (Icc (-1 : ℝ) 1) := by fun_prop
      exact (continuousOn_const.mul
        (Real.continuous_exp.comp_continuousOn harg)).mul
          (continuousOn_besselI1QuotientSeries a)
    have hmap : ContinuousOn (fun s : ℝ => s * R) (Icc (0 : ℝ) 1) :=
      continuousOn_id.mul continuousOn_const
    have hsub : MapsTo (fun s : ℝ => s * R) (Icc (0 : ℝ) 1)
        (Icc (-1 : ℝ) 1) := by
      intro s hs
      constructor
      · have habs : |s * R| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hs.1]
          nlinarith [mul_le_mul hs.2 hRabs (abs_nonneg R)
            (by norm_num : (0 : ℝ) ≤ 1)]
        exact (abs_le.mp habs).1
      · have habs : |s * R| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hs.1]
          nlinarith [mul_le_mul hs.2 hRabs (abs_nonneg R)
            (by norm_num : (0 : ℝ) ≤ 1)]
        exact (abs_le.mp habs).2
    have hcomp : ContinuousOn (fun s : ℝ => fourDLocalRadialFactor a (s * R))
        (Icc (0 : ℝ) 1) := hfactor.comp hmap hsub
    have hprod := (continuousOn_id.pow 3).mul hcomp
    have hprod' : ContinuousOn (fun s : ℝ => s ^ 3 *
        fourDLocalRadialFactor a (s * R)) (Icc (0 : ℝ) 1) := by
      convert hprod using 1
      · funext s
        simp
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hprod'
  have huniform' : TendstoUniformlyOn
      (fun R s : ℝ => s ^ 3 * fourDLocalRadialFactor a (s * R))
      (fun s : ℝ => s ^ 3 * fourDLocalRadialFactor a 0) (𝓝 0)
      (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using huniform
  have hlim := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) hcont huniform'
  have hmul : Tendsto (fun R : ℝ => (4 : ℝ) *
      ∫ s in (0 : ℝ)..1, s ^ 3 * fourDLocalRadialFactor a (s * R))
      (𝓝 0) (𝓝 ((4 : ℝ) *
        ∫ s in (0 : ℝ)..1, s ^ 3 * fourDLocalRadialFactor a 0)) :=
    tendsto_const_nhds.mul hlim
  have hpow : 4 * ∫ s in (0 : ℝ)..1, s ^ 3 = 1 := by
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => y ^ 4 / 4) (x ^ 3) x := by
      intro x _
      convert ((hasDerivAt_id' x).pow 4).div_const 4 using 1 <;> ring
    have hint : IntervalIntegrable (fun x : ℝ => x ^ 3) volume 0 1 := by
      exact ((continuous_id.pow 3).intervalIntegrable 0 1)
    calc
      4 * ∫ s in (0 : ℝ)..1, s ^ 3 =
          4 * ((fun y : ℝ => y ^ 4 / 4) 1 - (fun y : ℝ => y ^ 4 / 4) 0) := by
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      _ = 1 := by norm_num
  have hvalue : 4 * ∫ s in (0 : ℝ)..1,
      s ^ 3 * fourDLocalRadialFactor a 0 = fourDLocalRadialFactor a 0 := by
    rw [intervalIntegral.integral_mul_const, ← mul_assoc, hpow, one_mul]
  rw [hvalue] at hmul
  exact hmul

private theorem fourDWeightedIntervalIntegral_scale (g : ℝ → ℝ) (R : ℝ) :
    ∫ r in (0 : ℝ)..R, r ^ 3 * g r =
      R ^ 4 * ∫ s in (0 : ℝ)..1, s ^ 3 * g (s * R) := by
  have hscale := intervalIntegral.smul_integral_comp_mul_right
    (fun r : ℝ => r ^ 3 * g r) R (a := (0 : ℝ)) (b := 1)
  have hfactor : (∫ s in (0 : ℝ)..1, (s * R) ^ 3 * g (s * R)) =
      R ^ 3 * ∫ s in (0 : ℝ)..1, s ^ 3 * g (s * R) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, R ^ 3 * (s ^ 3 * g (s * R)) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = _ := intervalIntegral.integral_const_mul ..
  calc
    _ = R * ∫ s in (0 : ℝ)..1, (s * R) ^ 3 * g (s * R) := by
      simpa using hscale.symm
    _ = R ^ 4 * ∫ s in (0 : ℝ)..1, s ^ 3 * g (s * R) := by
      rw [hfactor]
      ring

/-- The actual two-row noncentral CDF is the lower mass of the radial kernel
already derived from the shifted Gaussian model. -/
private theorem noncentralTwoRowCDF_eq_fourDRadialIntegral
    (M : Matrix (Fin 2) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x)
    (hM : complexSampleMean M ≠ 0) :
    cdf ((stdGaussian (ComplexSample (m := 2) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      ∫ r in Ioc (0 : ℝ) (Real.sqrt (2 * x)),
        noncentralChiFourRadialKernel ‖complexSampleMean M‖ r := by
  have ha : 0 < ‖complexSampleMean M‖ := norm_pos_iff.mpr hM
  have hq := noncentralTwoRowCDF_eq_meanNormNuttallQ M x hx hM
  have hr := noncentralChiFourRadialLowerMass_eq_one_sub_nuttallQ21
    ‖complexSampleMean M‖ (Real.sqrt (2 * x)) ha (Real.sqrt_nonneg _)
  exact hq.trans hr.symm

/-- T4's first nontrivial actual-model specialization: for a nonzero complex
mean in a two-row, one-column Wishart sample, the CDF has hard-edge exponent
two and coefficient `exp (-‖complexSampleMean M‖²/2) / 2`. -/
theorem noncentralTwoRowCDF_div_tendsto_exp_neg_noncentrality_half
    (M : Matrix (Fin 2) (Fin 1) ℂ) (hM : complexSampleMean M ≠ 0) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (ComplexSample (m := 2) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x ^ 2)
      (𝓝[>] 0) (𝓝 ((1 / 2) * Real.exp
        (-(‖complexSampleMean M‖ ^ 2 / 2)))) := by
  let a : ℝ := ‖complexSampleMean M‖
  have ha : 0 < a := by dsimp [a]; exact norm_pos_iff.mpr hM
  have hg : ContinuousAt (fourDLocalRadialFactor a) 0 :=
    continuousAt_fourDLocalRadialFactor a
  have havg := fourDWeightedAverage_tendsto a
  have hR : Tendsto (fun x : ℝ => Real.sqrt (2 * x))
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hbase : ContinuousAt (fun x : ℝ => 2 * x) 0 := by fun_prop
    change Tendsto ((fun y : ℝ => Real.sqrt y) ∘ fun x : ℝ => 2 * x)
      (𝓝 0) (𝓝 0)
    simpa only [mul_zero, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hbase.tendsto)
  have hlimit := havg.comp hR
  have hfactor0 : fourDLocalRadialFactor a 0 =
      (1 / 2) * Real.exp (-(a ^ 2 / 2)) := fourDLocalRadialFactor_zero a
  have hfactor0' : fourDLocalRadialFactor a 0 =
      (1 / 2) * Real.exp
        (-(‖complexSampleMean M‖ ^ 2 / 2)) := by simpa [a] using hfactor0
  rw [hfactor0'] at hlimit
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  let R : ℝ := Real.sqrt (2 * x)
  have hRpos : 0 < R := by dsimp [R]; exact Real.sqrt_pos.2 (by positivity)
  have hRsq : R ^ 2 = 2 * x := by
    dsimp [R]
    exact Real.sq_sqrt (by positivity)
  have hCDF := noncentralTwoRowCDF_eq_fourDRadialIntegral M x hxpos.le hM
  have hkernel : ∀ r : ℝ,
      noncentralChiFourRadialKernel a r = r ^ 3 * fourDLocalRadialFactor a r := by
    intro r
    exact noncentralChiFourRadialKernel_eq_radius_cube_factor a r ha.ne'
  have hrew : ∫ r in (0 : ℝ)..R, r ^ 3 * fourDLocalRadialFactor a r =
      R ^ 4 * ∫ s in (0 : ℝ)..1,
        s ^ 3 * fourDLocalRadialFactor a (s * R) :=
    fourDWeightedIntervalIntegral_scale _ R
  have hrew' : ∫ r in (0 : ℝ)..Real.sqrt (2 * x),
      r ^ 3 * fourDLocalRadialFactor a r =
        (Real.sqrt (2 * x)) ^ 4 * ∫ s in (0 : ℝ)..1,
          s ^ 3 * fourDLocalRadialFactor a (s * Real.sqrt (2 * x)) := by
    simpa [R] using hrew
  have hkfun : (fun r : ℝ => noncentralChiFourRadialKernel
      ‖complexSampleMean M‖ r) =
      fun r => r ^ 3 * fourDLocalRadialFactor a r := by
    funext r
    simpa [a] using hkernel r
  symm
  change cdf ((stdGaussian (ComplexSample (m := 2) (n := 1))).map
    (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x ^ 2 = _
  rw [hCDF, ← intervalIntegral.integral_of_le (Real.sqrt_nonneg _), hkfun, hrew']
  have hsqrtSq : (Real.sqrt (2 * x)) ^ 2 = 2 * x :=
    Real.sq_sqrt (by positivity)
  have hRfour : (Real.sqrt (2 * x)) ^ 4 = 4 * x ^ 2 := by nlinarith [hsqrtSq]
  rw [hRfour]
  field_simp [ne_of_gt hxpos]
  simp only [Function.comp_apply]
  rw [show (2 : ℝ) * x = x * 2 by ring]

/-- The centered two-row model has the same exponent and coefficient, obtained
from its actual Gamma(2,1) law. -/
private theorem centralTwoRowCDF_div_tendsto_half :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (ComplexSample (m := 2) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin 2) (Fin 1) ℂ) (by norm_num))) x / x ^ 2)
      (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hgamma := cdf_gammaMeasure_nat_eq_lowerGamma 2 (by omega)
  have hweighted := normalized_weightedIntervalIntegral_tendsto
    (Real.continuous_exp.comp (continuous_neg.comp continuous_id))
  have hlimit : Tendsto (fun x : ℝ =>
      (1 / 2 : ℝ) * ((2 / x ^ 2) *
        ∫ u in (0 : ℝ)..x, u * Real.exp (-u)))
      (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    have hbase :=
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hweighted
    have hzero : Real.exp (-0 : ℝ) = 1 := by simp
    simpa [hzero] using hbase
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  rw [centralColumnSmallestEigenvalue_map_eq_gammaMeasure (m := 2) (by omega),
    hgamma x hxpos.le]
  field_simp [ne_of_gt hxpos]
  <;> ring

/-- Every two-row, one-column noncentral complex Wishart model, including the
centered boundary, has the expected T4 hard-edge asymptotic. -/
theorem noncentralTwoRowCDF_div_tendsto_exp_neg_noncentrality_half_anyMean
    (M : Matrix (Fin 2) (Fin 1) ℂ) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (ComplexSample (m := 2) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x ^ 2)
      (𝓝[>] 0) (𝓝 ((1 / 2) * Real.exp
        (-(‖complexSampleMean M‖ ^ 2 / 2)))) := by
  by_cases hzero : complexSampleMean M = 0
  · have hMzero : M = 0 := by
      have h := complexSampleMatrix_add_mean
        (0 : ComplexSample (m := 2) (n := 1)) M
      rw [hzero] at h
      simpa [complexSampleMatrix] using h.symm
    rw [hMzero]
    have hmean0 : complexSampleMean
        (0 : Matrix (Fin 2) (Fin 1) ℂ) = 0 := by
      ext ij
      simp [complexSampleMean]
    rw [hmean0]
    simpa using centralTwoRowCDF_div_tendsto_half
  · exact noncentralTwoRowCDF_div_tendsto_exp_neg_noncentrality_half M hzero
    

end

end JinWishart
