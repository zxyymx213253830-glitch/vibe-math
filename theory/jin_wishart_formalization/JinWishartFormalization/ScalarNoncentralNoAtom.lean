import JinWishartFormalization.ScalarNoncentralCDFRice
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# No atoms in the scalar noncentral Wishart law

The unique Gram eigenvalue of a `1 × 1` complex Gaussian sample is a
translated Euclidean squared norm. Its level sets are spheres, which
have zero Gaussian mass because the Gaussian has a Lebesgue density.
-/

open Matrix MeasureTheory ProbabilityTheory Set

namespace JinWishart

theorem noncentralScalarEigenvalue_eq_shiftedNormSq
    (M : Matrix (Fin 1) (Fin 1) ℂ)
    (z : ComplexSample (m := 1) (n := 1)) :
    complexNoncentralSampleSmallestEigenvalue M (by norm_num) z =
      ‖z + complexSampleMean M‖ ^ 2 / 2 := by
  rw [noncentralScalarSmallestEigenvalue_eq_shiftedEnergy]
  have hscalar : centralScalarSampleEnergy (z + complexSampleMean M) =
      centralColumnSampleEnergy (z + complexSampleMean M) := by
    simp [centralScalarSampleEnergy, centralColumnSampleEnergy]
  rw [hscalar, centralColumnSampleEnergy_eq_euclideanEnergy]

theorem stdGaussian_scalar_sphere_zero
    (c : ComplexSample (m := 1) (n := 1)) (R : ℝ) :
    stdGaussian (ComplexSample (m := 1) (n := 1))
      (Metric.sphere c R) = 0 := by
  rw [stdGaussian_euclidean_eq_radialDensity]
  exact withDensity_absolutelyContinuous volume _
    (Measure.addHaar_sphere
      (volume : Measure (ComplexSample (m := 1) (n := 1))) c R)

theorem noncentralScalarEigenvalue_noAtom
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) :
    ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) {x} = 0 := by
  rw [Measure.map_apply
    (measurable_complexNoncentralSampleSmallestEigenvalue M (by norm_num))
    (measurableSet_singleton x)]
  by_cases hx : 0 ≤ x
  · have hevent :
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num)) ⁻¹' {x} =
          Metric.sphere (-complexSampleMean M) (Real.sqrt (2 * x)) := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, Metric.mem_sphere,
        dist_eq_norm, sub_neg_eq_add]
      rw [noncentralScalarEigenvalue_eq_shiftedNormSq]
      have hs : Real.sqrt (2 * x) ^ 2 = 2 * x := Real.sq_sqrt (by positivity)
      constructor
      · intro h
        apply (sq_eq_sq₀ (norm_nonneg (z + complexSampleMean M))
          (Real.sqrt_nonneg _)).mp
        nlinarith [h, hs]
      · intro h
        have hsq := (sq_eq_sq₀ (norm_nonneg (z + complexSampleMean M))
          (Real.sqrt_nonneg _)).mpr h
        nlinarith [hs, hsq]
    rw [hevent]
    exact stdGaussian_scalar_sphere_zero _ _
  · have hevent :
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num)) ⁻¹' {x} =
          (∅ : Set (ComplexSample (m := 1) (n := 1))) := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rw [noncentralScalarEigenvalue_eq_shiftedNormSq]
      have hnonneg : 0 ≤ ‖z + complexSampleMean M‖ ^ 2 / 2 := by positivity
      exact ne_of_gt (lt_of_not_ge hx |>.trans_le hnonneg)
    rw [hevent]
    exact measure_empty

/-- The scalar noncentral CDF agrees with the strict sublevel probability,
since its eigenvalue law has no atoms. -/
theorem noncentralScalarCDF_eq_strictSublevelMass
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      (((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))).real (Iio x)) := by
  let ν : Measure ℝ := (stdGaussian (ComplexSample (m := 1) (n := 1))).map
    (complexNoncentralSampleSmallestEigenvalue M (by norm_num))
  have hset : Iic x = Iio x ∪ {x} := by
    ext y
    simp [le_iff_lt_or_eq]
  rw [cdf_eq_real, measureReal_def, hset,
    measure_union (by grind) (measurableSet_singleton x)]
  rw [noncentralScalarEigenvalue_noAtom M x]
  simp [measureReal_def]

end JinWishart
