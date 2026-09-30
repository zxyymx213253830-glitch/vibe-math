import JinWishartFormalization.NoncentralOneColumnEnergy
import JinWishartFormalization.NoncentralEightDimensionalRadial

/-!
# The actual 4×1 complex sample in eight real coordinates

The sample model already encodes each complex entry by its real and imaginary
Gaussian coordinates.  This module reindexes those eight coordinates by `Fin 8`,
placing the real part of the first row first, and carries the axial-mean ball
event to the eight-dimensional Gaussian radial theorem.  The resulting actual
CDF theorem is for an axial mean and is stated as a finite radial-series
integral; the full Nuttall-Q tail normalization remains separate.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

/-- Reindex the eight real coordinates of a four-row, one-column sample so
that the first real coordinate of the sample is coordinate zero. -/
def fourRowSampleIndexEquiv : ((Fin 4 × Fin 1) × Fin 2) ≃ Fin 8 := by
  let e := Fintype.equivFinOfCardEq
    (show Fintype.card (((Fin 4 × Fin 1) × Fin 2)) = 8 by simp)
  exact e.trans (Equiv.swap (e ((0, 0), 0)) 0)

/-- Isometry from the actual sample space to eight real Euclidean coordinates. -/
def fourRowSampleToFin8 :
    ComplexSample (m := 4) (n := 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ fourRowSampleIndexEquiv

theorem stdGaussian_map_fourRowSampleToFin8 :
    (stdGaussian (ComplexSample (m := 4) (n := 1))).map fourRowSampleToFin8 =
      stdGaussian (EuclideanSpace ℝ (Fin 8)) :=
  stdGaussian_map fourRowSampleToFin8

/-- A four-row complex mean supported on the real component of its first
entry, normalized so its encoded real mean has amplitude `a`. -/
def fourRowAxialMean (a : ℝ) : Matrix (Fin 4) (Fin 1) ℂ :=
  fun i _ => if i = 0 then (a / Real.sqrt 2 : ℝ) else 0

private theorem fourRowAxialSampleMean_coord (a : ℝ)
    (i : (Fin 4 × Fin 1) × Fin 2) :
    complexSampleMean (fourRowAxialMean a) i =
      if i = ((0, 0), 0) then a else 0 := by
  rcases i with ⟨⟨i, j⟩, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [complexSampleMean, fourRowAxialMean] <;>
    (have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
     calc
       Real.sqrt 2 * (a / Real.sqrt 2) =
           a * (Real.sqrt 2 * (Real.sqrt 2)⁻¹) := by ring
       _ = a := by rw [mul_inv_cancel₀ hs, mul_one])

theorem fourRowSampleToFin8_complexSampleMean (a : ℝ) :
    fourRowSampleToFin8 (complexSampleMean (fourRowAxialMean a)) =
      a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ) := by
  ext k
  have hzero : fourRowSampleIndexEquiv.symm 0 = ((0, 0), 0) := by
    simp [fourRowSampleIndexEquiv]
  have hpre (k : Fin 8) :
      fourRowSampleIndexEquiv.symm k = ((0, 0), 0) ↔ k = 0 := by
    constructor
    · intro h
      have := congrArg fourRowSampleIndexEquiv h
      simpa [fourRowSampleIndexEquiv] using this
    · intro hk
      rw [hk, hzero]
  simp [fourRowSampleToFin8, LinearIsometryEquiv.piLpCongrLeft_apply,
    fourRowAxialSampleMean_coord, hpre, EuclideanSpace.single_apply]

/-- The actual shifted-ball event for the axial `4×1` complex sample maps to
the corresponding centered ball in E₈ under the standard Gaussian isometry. -/
theorem fourRowAxialShiftedBall_eq_eightDBall (a R : ℝ) :
    (stdGaussian (ComplexSample (m := 4) (n := 1)))
        (Metric.closedBall (-complexSampleMean (fourRowAxialMean a)) R) =
      (stdGaussian (EuclideanSpace ℝ (Fin 8)))
        (Metric.closedBall
          (-(a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ))) R) := by
  rw [← stdGaussian_map_fourRowSampleToFin8]
  rw [Measure.map_apply (fourRowSampleToFin8.continuous.measurable)
    measurableSet_closedBall]
  have hball := fourRowSampleToFin8.preimage_closedBall
    (-(a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ))) R
  rw [hball]
  congr 1
  rw [← fourRowSampleToFin8_complexSampleMean]
  simp

/-- The coordinate isometry carries a shifted ball for any complex mean
matrix to the corresponding shifted E₈ ball. -/
theorem fourRowSampleShiftedBall_eq_eightDBall
    (M : Matrix (Fin 4) (Fin 1) ℂ) (R : ℝ) :
    (stdGaussian (ComplexSample (m := 4) (n := 1)))
        (Metric.closedBall (-complexSampleMean M) R) =
      (stdGaussian (EuclideanSpace ℝ (Fin 8)))
        (Metric.closedBall (-(fourRowSampleToFin8 (complexSampleMean M))) R) := by
  rw [← stdGaussian_map_fourRowSampleToFin8]
  rw [Measure.map_apply (fourRowSampleToFin8.continuous.measurable)
    measurableSet_closedBall]
  have hball := fourRowSampleToFin8.preimage_closedBall
    (-(fourRowSampleToFin8 (complexSampleMean M))) R
  rw [hball]
  congr 1
  simp

/-- Rotational invariance of the eight-dimensional standard Gaussian reduces
any nonzero shifted ball to the first-axis shift of the same amplitude. -/
theorem stdGaussian_eightDBall_shift_eq_axial
    (μ : EuclideanSpace ℝ (Fin 8)) (hμ : μ ≠ 0) (R : ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin 8))) (Metric.closedBall (-μ) R) =
      (stdGaussian (EuclideanSpace ℝ (Fin 8)))
        (Metric.closedBall
          (-(‖μ‖ • EuclideanSpace.single (0 : Fin 8) (1 : ℝ))) R) := by
  classical
  let s : Set (Fin 8) := {0}
  let v : Fin 8 → EuclideanSpace ℝ (Fin 8) := fun i =>
    if i = 0 then ‖μ‖⁻¹ • μ else 0
  have hμnorm : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have hvnorm : ‖‖μ‖⁻¹ • μ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμnorm)]
    simp [hμnorm.ne']
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    have hi : (i : Fin 8) = 0 := by
      exact Set.mem_singleton_iff.mp (by simpa [s] using i.property)
    simpa [v, hi] using hvnorm
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = Fintype.card (Fin 8) by simp)
      (s := s) (v := v) hv
  have hb0 : b 0 = ‖μ‖⁻¹ • μ := by
    have h := hb 0 (by simp [s])
    simpa [v] using h
  have hμrepr : μ = ‖μ‖ • b 0 := by
    rw [hb0]
    simp [smul_smul, hμnorm.ne']
  have hmap : b.repr μ =
      ‖μ‖ • EuclideanSpace.single (0 : Fin 8) (1 : ℝ) := by
    calc
      b.repr μ = b.repr (‖μ‖ • b 0) := congrArg b.repr hμrepr
      _ = ‖μ‖ • b.repr (b 0) := map_smul b.repr ‖μ‖ (b 0)
      _ = ‖μ‖ • EuclideanSpace.single 0 1 := by rw [b.repr_self]
  calc
    (stdGaussian (EuclideanSpace ℝ (Fin 8))) (Metric.closedBall (-μ) R) =
        ((stdGaussian (EuclideanSpace ℝ (Fin 8))).map b.repr)
          (Metric.closedBall (b.repr (-μ)) R) := by
      rw [Measure.map_apply b.repr.continuous.measurable measurableSet_closedBall]
      rw [b.repr.preimage_closedBall (b.repr (-μ)) R]
      simp
    _ = (stdGaussian (EuclideanSpace ℝ (Fin 8)))
          (Metric.closedBall (b.repr (-μ)) R) := by rw [stdGaussian_map]
    _ = (stdGaussian (EuclideanSpace ℝ (Fin 8)))
          (Metric.closedBall
            (-(‖μ‖ • EuclideanSpace.single (0 : Fin 8) (1 : ℝ))) R) := by
      rw [map_neg, hmap]

/-- The eight-real-dimensional standard Gaussian normalizer is `(2π)⁻⁴`. -/
theorem stdGaussianEightD_normalizer_eq :
    (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin 8) =
      (2 * Real.pi)⁻¹ ^ 4 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hsquare : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt hp.le
  rw [Fintype.card_fin]
  have height : (Real.sqrt (2 * Real.pi)) ^ 8 = (2 * Real.pi) ^ 4 := by
    rw [show 8 = 2 * 4 by norm_num, pow_mul, hsquare]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ ^ 8 =
        ((Real.sqrt (2 * Real.pi)) ^ 8)⁻¹ := by rw [← inv_pow]
    _ = ((2 * Real.pi) ^ 4)⁻¹ := by rw [height]
    _ = (2 * Real.pi)⁻¹ ^ 4 := by rw [inv_pow]

/-- Probability under the actual eight-dimensional standard Gaussian of an
axially shifted ball equals the lower mass of the derived radial series. -/
theorem stdGaussianEightDBall_axialMeasure_eq_radialSeriesCDF
    (a R : ℝ) (hR : 0 ≤ R) :
    (stdGaussian (EuclideanSpace ℝ (Fin 8))).real
        (Metric.closedBall
          (-(a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ))) R) =
      ∫ r in Ioc (0 : ℝ) R, noncentralChiEvenRadialKernel 3 a r := by
  let μ : EuclideanSpace ℝ (Fin 8) :=
    a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)
  calc
    _ = ∫ z in Metric.closedBall (-μ) R,
        euclideanStdGaussianDensity z :=
      stdGaussian_euclidean_ball_real_eq_densityIntegral (-μ) R
    _ = ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) R,
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin 8) *
          Real.exp (-‖z - μ‖ ^ 2 / 2) :=
      integral_euclideanGaussian_shiftedBall_eq_centered μ R
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin 8) *
        (∫ z : EuclideanSpace ℝ (Fin 8),
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) R).indicator
            (fun z => Real.exp (-‖z - μ‖ ^ 2 / 2)) z
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 8)))) := by
      rw [integral_const_mul, ← integral_indicator measurableSet_closedBall]
    _ = (2 * Real.pi)⁻¹ ^ 4 *
        (∫ z : EuclideanSpace ℝ (Fin 8),
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) R).indicator
            (fun z => Real.exp (-‖z - μ‖ ^ 2 / 2)) z
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 8)))) := by
      rw [stdGaussianEightD_normalizer_eq]
    _ = ∫ r in Ioc (0 : ℝ) R, noncentralChiEvenRadialKernel 3 a r := by
      simpa [μ] using
        stdGaussianEightDBall_axial_eq_radialSeriesCDF a R hR

/-- Actual `4×1` noncentral one-column weak CDF for an axial rank-one mean,
expressed as the finite-radius mass of the proven order-three radial series. -/
theorem noncentralFourRowAxialCDF_eq_radialSeries
    (a x : ℝ) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := 4) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (fourRowAxialMean a) (by norm_num))) x =
      ∫ r in Ioc (0 : ℝ) (Real.sqrt (2 * x)),
        noncentralChiEvenRadialKernel 3 a r := by
  rw [cdf_eq_real, measureReal_def]
  rw [noncentralColumnSmallestEigenvalue_sublevelMass_eq_shiftedBall
    (m := 4) (by norm_num) (fourRowAxialMean a) x hx]
  rw [fourRowAxialShiftedBall_eq_eightDBall]
  rw [← measureReal_def]
  exact stdGaussianEightDBall_axialMeasure_eq_radialSeriesCDF a
    (Real.sqrt (2 * x)) (Real.sqrt_nonneg _)

/-- Actual 4×1 noncentral one-column weak CDF for an arbitrary deterministic
mean matrix. The only parameter is the norm of its encoded real mean vector. -/
theorem noncentralFourRowCDF_eq_radialSeries_of_mean
    (M : Matrix (Fin 4) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := 4) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      ∫ r in Ioc (0 : ℝ) (Real.sqrt (2 * x)),
        noncentralChiEvenRadialKernel 3
          ‖fourRowSampleToFin8 (complexSampleMean M)‖ r := by
  rw [cdf_eq_real, measureReal_def]
  rw [noncentralColumnSmallestEigenvalue_sublevelMass_eq_shiftedBall
    (m := 4) (by norm_num) M x hx]
  rw [fourRowSampleShiftedBall_eq_eightDBall]
  by_cases hμ : fourRowSampleToFin8 (complexSampleMean M) = 0
  · have hnorm : ‖fourRowSampleToFin8 (complexSampleMean M)‖ = 0 := by
      rw [hμ]
      simp
    rw [hμ]
    rw [show -(0 : EuclideanSpace ℝ (Fin 8)) =
      -(‖(0 : EuclideanSpace ℝ (Fin 8))‖ •
        EuclideanSpace.single (0 : Fin 8) (1 : ℝ)) by simp]
    rw [← measureReal_def]
    simpa using stdGaussianEightDBall_axialMeasure_eq_radialSeriesCDF 0
      (Real.sqrt (2 * x)) (Real.sqrt_nonneg _)
  · have hrot := stdGaussian_eightDBall_shift_eq_axial
      (fourRowSampleToFin8 (complexSampleMean M)) hμ (Real.sqrt (2 * x))
    rw [hrot, ← measureReal_def]
    exact stdGaussianEightDBall_axialMeasure_eq_radialSeriesCDF
      ‖fourRowSampleToFin8 (complexSampleMean M)‖
      (Real.sqrt (2 * x)) (Real.sqrt_nonneg _)

end

end JinWishart



