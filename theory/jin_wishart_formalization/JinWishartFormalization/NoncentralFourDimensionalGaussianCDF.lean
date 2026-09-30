import JinWishartFormalization.GaussianEuclideanBallDensity
import JinWishartFormalization.NoncentralFourDimensionalCDF

/-!
# Actual four-dimensional Gaussian ball probability

This module closes the density-to-probability bridge for the axial
noncentral `2×1` model: the event is evaluated under Mathlib's standard
Gaussian measure, then identified with the normalized Nuttall-Q formula.
-/

open MeasureTheory Set ProbabilityTheory

namespace JinWishart

noncomputable section

/-- In four real coordinates, the standard Gaussian normalizer is exactly
`(2π)⁻²`, the coefficient used by the radial-kernel theorem. -/
theorem stdGaussianFourD_normalizer_eq :
    (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin 4) =
      (2 * Real.pi)⁻¹ ^ 2 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hsquare : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt hp.le
  rw [Fintype.card_fin]
  field_simp [hs, Real.pi_ne_zero]
  nlinarith [hsquare]

/-- The real four-dimensional shifted standard Gaussian ball probability, for
an axial mean of amplitude `a>0`, equals the normalized `Q_{2,1}` CDF. This is
the actual probability measure of the Gaussian sample, not a separately
postulated radial distribution. -/
theorem stdGaussian_fourDBall_axial_eq_one_sub_nuttallQ21
    (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) :
    (stdGaussian (EuclideanSpace ℝ (Fin 4))).real
        (Metric.closedBall
          (-(a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ))) R) =
      1 - (nuttallQ 2 1 a R / (a : ℂ)).re := by
  let μ : EuclideanSpace ℝ (Fin 4) :=
    a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)
  calc
    _ = ∫ z in Metric.closedBall (-μ) R,
        euclideanStdGaussianDensity z :=
      stdGaussian_euclidean_ball_real_eq_densityIntegral (-μ) R
    _ = ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R,
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin 4) *
          Real.exp (-‖z - μ‖ ^ 2 / 2) := by
      exact integral_euclideanGaussian_shiftedBall_eq_centered μ R
    _ = (2 * Real.pi)⁻¹ ^ 2 *
        (∫ z : EuclideanSpace ℝ (Fin 4),
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
            (fun z => Real.exp (-‖z - μ‖ ^ 2 / 2)) z
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 4)))) := by
      rw [integral_const_mul, ← integral_indicator measurableSet_closedBall,
        stdGaussianFourD_normalizer_eq]
    _ = 1 - (nuttallQ 2 1 a R / (a : ℂ)).re := by
      simpa [μ] using shiftedGaussianFourDBallIntegral_eq_one_sub_nuttallQ21
        a R ha hR

/-- Any nonzero shift in four dimensions can be rotated to the first axis by
extending its unit direction to an orthonormal basis. Standard Gaussian ball
probability therefore depends on the shift only through its norm. -/
theorem stdGaussian_fourDBall_shift_eq_axial
    (μ : EuclideanSpace ℝ (Fin 4)) (hμ : μ ≠ 0) (R : ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin 4)))
        (Metric.closedBall (-μ) R) =
      (stdGaussian (EuclideanSpace ℝ (Fin 4)))
        (Metric.closedBall
          (-(‖μ‖ • EuclideanSpace.single (0 : Fin 4) (1 : ℝ))) R) := by
  classical
  let s : Set (Fin 4) := {0}
  let v : Fin 4 → EuclideanSpace ℝ (Fin 4) := fun i =>
    if i = 0 then ‖μ‖⁻¹ • μ else 0
  have hμnorm : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have hvnorm : ‖‖μ‖⁻¹ • μ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμnorm)]
    simp [hμnorm.ne']
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    have hi : (i : Fin 4) = 0 := by
      exact Set.mem_singleton_iff.mp (by simpa [s] using i.property)
    simpa [v, hi] using hvnorm
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = Fintype.card (Fin 4) by simp)
      (s := s) (v := v) hv
  have hb0 : b 0 = ‖μ‖⁻¹ • μ := by
    have h := hb 0 (by simp [s])
    simpa [v] using h
  have hμrepr : μ = ‖μ‖ • b 0 := by
    rw [hb0]
    simp [smul_smul, hμnorm.ne']
  have hmap : b.repr μ =
      ‖μ‖ • EuclideanSpace.single (0 : Fin 4) (1 : ℝ) := by
    calc
      b.repr μ = b.repr (‖μ‖ • b 0) := congrArg b.repr hμrepr
      _ = ‖μ‖ • b.repr (b 0) := map_smul b.repr ‖μ‖ (b 0)
      _ = ‖μ‖ • EuclideanSpace.single 0 1 := by rw [b.repr_self]
  calc
    (stdGaussian (EuclideanSpace ℝ (Fin 4))) (Metric.closedBall (-μ) R) =
        ((stdGaussian (EuclideanSpace ℝ (Fin 4))).map b.repr)
          (Metric.closedBall (b.repr (-μ)) R) := by
      rw [Measure.map_apply b.repr.continuous.measurable measurableSet_closedBall]
      rw [b.repr.preimage_closedBall (b.repr (-μ)) R]
      simp
    _ = (stdGaussian (EuclideanSpace ℝ (Fin 4)))
          (Metric.closedBall (b.repr (-μ)) R) := by rw [stdGaussian_map]
    _ = (stdGaussian (EuclideanSpace ℝ (Fin 4)))
          (Metric.closedBall
            (-(‖μ‖ • EuclideanSpace.single (0 : Fin 4) (1 : ℝ))) R) := by
      rw [map_neg]
      rw [hmap]

/-- The actual four-dimensional shifted Gaussian ball probability for any
nonzero mean is the normalized `Q_{2,1}` formula with amplitude equal to the
Euclidean norm of that mean. -/
theorem stdGaussian_fourDBall_anyMean_eq_one_sub_nuttallQ21
    (μ : EuclideanSpace ℝ (Fin 4)) (hμ : μ ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    (stdGaussian (EuclideanSpace ℝ (Fin 4))).real
        (Metric.closedBall (-μ) R) =
      1 - (nuttallQ 2 1 ‖μ‖ R / (‖μ‖ : ℂ)).re := by
  have ha : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have hrot := stdGaussian_fourDBall_shift_eq_axial μ hμ R
  have hrotReal := congrArg ENNReal.toReal hrot
  exact hrotReal.trans <| stdGaussian_fourDBall_axial_eq_one_sub_nuttallQ21
    ‖μ‖ R ha hR

end

end JinWishart
