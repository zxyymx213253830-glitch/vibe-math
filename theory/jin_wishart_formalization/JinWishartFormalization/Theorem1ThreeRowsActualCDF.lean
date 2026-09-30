import JinWishartFormalization.Theorem1SingleColumnAnyRows
import JinWishartFormalization.NoncentralThreeRowNuttallQ

/-!
# Theorem 1 for the actual three-row, one-column model

For positive noncentrality, the order-`(3,2)` Nuttall integrand is exactly a
real nonnegative multiple of the six-dimensional radial density. This makes
the complex Nuttall tail real and identifies its value at zero with `a^2`.
Consequently the normalized-norm candidate in Theorem 1 is the actual CDF.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

/-- The `(3,2)` Nuttall integrand is real and equals `a²` times the actual
six-dimensional radial density. This is the crucial bridge that justifies
replacing a complex norm by a real nonnegative tail; it is not inferred merely
from the real-part identity. -/
theorem nuttallQ32Integrand_eq_ofReal_scaledRadialKernel
    (a r : ℝ) (ha : a ≠ 0) :
    nuttallQIntegrand 3 2 a r =
      ((a ^ 2 * noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) := by
  have hdiv := (noncentralChiSixRadialSeriesKernel_eq_nuttallQ32_div_sq
    a r ha).symm
  calc
    nuttallQIntegrand 3 2 a r =
        (a : ℂ) ^ 2 *
          (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2) := by
      field_simp [ha]
    _ = (a : ℂ) ^ 2 *
          (noncentralChiSixRadialSeriesKernel a r : ℂ) := by rw [hdiv]
    _ = ((a ^ 2 * noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-- On every nonnegative upper tail, the complex Nuttall integral is the real
tail mass multiplied by `a²`. -/
theorem nuttallQ32_eq_ofReal_scaledRadialTail
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 ≤ b) :
    nuttallQ 3 2 a b =
      ((a ^ 2 * ∫ r in Ioi b,
        noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) := by
  have hreal : IntegrableOn
      (fun r : ℝ => a ^ 2 * noncentralChiSixRadialSeriesKernel a r)
      (Ioi b) :=
    (integrableOn_noncentralChiSixRadialSeriesKernel a).mono_set
      (Ioi_subset_Ioi hb) |>.const_mul (a ^ 2)
  have hcomplex : IntegrableOn
      (fun r : ℝ =>
        ((a ^ 2 * noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ))
      (Ioi b) := Complex.ofRealCLM.integrable_comp hreal
  have hQint : IntegrableOn (nuttallQIntegrand 3 2 a) (Ioi b) := by
    apply (integrableOn_congr_fun (s := Ioi b) ?_ measurableSet_Ioi).2 hcomplex
    intro r _
    exact nuttallQ32Integrand_eq_ofReal_scaledRadialKernel a r ha
  unfold nuttallQ
  calc
    (∫ r in Ioi b, nuttallQIntegrand 3 2 a r) =
        ∫ r in Ioi b,
          ((a ^ 2 * noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with r
      exact nuttallQ32Integrand_eq_ofReal_scaledRadialKernel a r ha
    _ = ((∫ r in Ioi b,
          a ^ 2 * noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = ((a ^ 2 * ∫ r in Ioi b,
          noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) := by
      rw [integral_const_mul]

/-- The zero-threshold Nuttall value is exactly `a²`, not just a quantity
whose real part is `a²`. -/
theorem nuttallQ32_zero_eq_sq (a : ℝ) (ha : a ≠ 0) :
    nuttallQ 3 2 a 0 = (a ^ 2 : ℂ) := by
  rw [nuttallQ32_eq_ofReal_scaledRadialTail a 0 ha (le_refl 0)]
  rw [noncentralChiSixRadialSeriesKernel_integral_eq_one]
  simp

/-- The complex norm of the Nuttall tail is its real nonnegative radial mass
times `a²`. -/
theorem norm_nuttallQ32_eq_sq_mul_radialTail
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 ≤ b) :
    ‖nuttallQ 3 2 a b‖ =
      a ^ 2 * ∫ r in Ioi b,
        noncentralChiSixRadialSeriesKernel a r := by
  rw [nuttallQ32_eq_ofReal_scaledRadialTail a b ha hb,
    Complex.norm_real, Real.norm_eq_abs]
  have htail : 0 ≤ ∫ r in Ioi b,
      noncentralChiSixRadialSeriesKernel a r :=
    setIntegral_nonneg measurableSet_Ioi fun r hr =>
      noncentralChiSixRadialSeriesKernel_nonneg a r
        (le_of_lt (lt_of_le_of_lt hb hr))
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg a) htail)]

/-- Theorem 1's one-column candidate for `(s,t,L)=(1,3,1)` is the actual
smallest-eigenvalue CDF of the complex noncentral Wishart sample, for a
positive noncentrality parameter. Here `a=sqrt(2 lambda)` is the norm of the
axial mean, so the paper's `lambda` is `a²/2`. -/
theorem theorem1ThreeRowsOneColumnCandidate_eq_actualAxialCDF
    (lambda x : ℝ) (hlambda : 0 < lambda) (hx : 0 ≤ x) :
    theorem1CdfCandidate 1 3 1 (by omega) (by omega)
        (fun _ : Fin 1 => lambda) x =
      cdf ((stdGaussian (ComplexSample (m := 3) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (threeRowAxialMean (Real.sqrt (2 * lambda))) (by norm_num))) x := by
  let a : ℝ := Real.sqrt (2 * lambda)
  let b : ℝ := Real.sqrt (2 * x)
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 (by positivity)
  have hb : 0 ≤ b := by dsimp [b]; exact Real.sqrt_nonneg _
  have hqzero : nuttallQ 3 2 a 0 = (a ^ 2 : ℂ) :=
    nuttallQ32_zero_eq_sq a ha.ne'
  have hden : nuttallQ 3 2 a 0 ≠ 0 := by
    rw [hqzero]
    exact_mod_cast (pow_ne_zero 2 ha.ne')
  have hnormzero : ‖nuttallQ 3 2 a 0‖ = a ^ 2 := by
    rw [hqzero, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sq_pos_of_ne_zero ha.ne')]
  have hratio :
      ‖nuttallQ 3 2 a b‖ / ‖nuttallQ 3 2 a 0‖ =
        ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r := by
    rw [norm_nuttallQ32_eq_sq_mul_radialTail a b ha.ne' hb, hnormzero]
    field_simp [ne_of_gt (sq_pos_of_ne_zero ha.ne')]
  have htail :
      (∫ r in Ioi b,
        (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2).re) =
      ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r := by
    apply integral_congr_ae
    filter_upwards with r
    have h := noncentralChiSixRadialSeriesKernel_eq_nuttallQ32_div_sq a r ha.ne'
    have hre := congrArg Complex.re h
    simpa using hre.symm
  rw [theorem1OneColumnCandidate_eq_normalizedNuttallQ
    3 (by omega) lambda x hden]
  simp only [theorem1OneColumnNuttallQ, a, b]
  rw [noncentralThreeRowAxialCDF_eq_one_sub_nuttallQ32Tail
    (Real.sqrt (2 * lambda)) x hx (ne_of_gt ha)]
  rw [hratio, ← htail]

/-- Arbitrary-mean form of the same `(1,3,1)` closure. The only parameter
compatibility assumption is the paper's noncentrality convention: `lambda` is
half the squared norm of the six-real-coordinate encoded mean. Rotational
invariance has already been formalized by the arbitrary-mean CDF/radial-tail
theorem. -/
theorem theorem1ThreeRowsOneColumnCandidate_eq_actualCDF
    (M : Matrix (Fin 3) (Fin 1) ℂ) (lambda x : ℝ)
    (hlambda : 0 < lambda) (hx : 0 ≤ x)
    (hmean : ‖threeRowSampleToFin6 (complexSampleMean M)‖ ^ 2 =
      2 * lambda) :
    theorem1CdfCandidate 1 3 1 (by omega) (by omega)
        (fun _ : Fin 1 => lambda) x =
      cdf ((stdGaussian (ComplexSample (m := 3) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x := by
  let a : ℝ := ‖threeRowSampleToFin6 (complexSampleMean M)‖
  let b : ℝ := Real.sqrt (2 * x)
  have hamp : a = Real.sqrt (2 * lambda) := by
    dsimp [a]
    calc
      ‖threeRowSampleToFin6 (complexSampleMean M)‖ =
          Real.sqrt (‖threeRowSampleToFin6 (complexSampleMean M)‖ ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt (2 * lambda) := by rw [hmean]
  have ha : 0 < a := by rw [hamp]; exact Real.sqrt_pos.2 (by positivity)
  have hb : 0 ≤ b := by dsimp [b]; exact Real.sqrt_nonneg _
  have hqzero : nuttallQ 3 2 a 0 = (a ^ 2 : ℂ) :=
    nuttallQ32_zero_eq_sq a ha.ne'
  have hden : nuttallQ 3 2 (Real.sqrt (2 * lambda)) 0 ≠ 0 := by
    rw [← hamp, hqzero]
    exact_mod_cast (pow_ne_zero 2 ha.ne')
  have hnormzero : ‖nuttallQ 3 2 a 0‖ = a ^ 2 := by
    rw [hqzero, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sq_pos_of_ne_zero ha.ne')]
  have hratio :
      ‖nuttallQ 3 2 a b‖ / ‖nuttallQ 3 2 a 0‖ =
        ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r := by
    rw [norm_nuttallQ32_eq_sq_mul_radialTail a b ha.ne' hb, hnormzero]
    field_simp [ne_of_gt (sq_pos_of_ne_zero ha.ne')]
  have htail :
      (∫ r in Ioi b,
        (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2).re) =
      ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r := by
    apply integral_congr_ae
    filter_upwards with r
    have h := noncentralChiSixRadialSeriesKernel_eq_nuttallQ32_div_sq a r ha.ne'
    have hre := congrArg Complex.re h
    simpa using hre.symm
  have hAmpNZ :
      ‖threeRowSampleToFin6 (complexSampleMean M)‖ ≠ 0 := by
    dsimp [a] at ha
    exact ha.ne'
  rw [theorem1OneColumnCandidate_eq_normalizedNuttallQ
    3 (by omega) lambda x hden]
  simp only [theorem1OneColumnNuttallQ, Nat.reduceSub]
  rw [← hamp]
  rw [noncentralThreeRowCDF_eq_one_sub_nuttallQ32Tail_of_mean
    M x hx hAmpNZ]
  simp only [a, b]
  rw [hratio, ← htail]

end

end JinWishart
