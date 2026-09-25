import JinWishartFormalization.GaussianRadialLaw
import JinWishartFormalization.WishartProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# No atoms for a one-column noncentral complex Wishart law

For any positive number of sample rows, its sole Gram eigenvalue is the
squared Euclidean norm of a translated Gaussian vector.  Its level sets are
spheres, which have zero mass under a measure with a Lebesgue density.
-/

open Matrix MeasureTheory ProbabilityTheory Set

namespace JinWishart

/-- For one column, the unique noncentral Gram eigenvalue is the energy of the
translated real Gaussian coordinate vector. -/
theorem oneColumnNoncentralEigenvalue_eq_shiftedNormSq {m : ℕ} (hm : 0 < m)
    (M : Matrix (Fin m) (Fin 1) ℂ)
    (z : ComplexSample (m := m) (n := 1)) :
    complexNoncentralSampleSmallestEigenvalue M (by norm_num)
      (z : ComplexSample (m := m) (n := 1)) =
      ‖z + complexSampleMean M‖ ^ 2 / 2 := by
  have hshift : complexSampleMatrix (z + complexSampleMean M) =
      complexSampleMatrix z + M := complexSampleMatrix_add_mean z M
  have hcentral :
      complexNoncentralSampleSmallestEigenvalue M (by norm_num) z =
        complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin m) (Fin 1) ℂ)
          (by norm_num) (z + complexSampleMean M) := by
    simp [complexNoncentralSampleSmallestEigenvalue, hshift]
  rw [hcentral, centralColumnSampleSmallestEigenvalue_eq_energy hm,
    centralColumnSampleEnergy_eq_euclideanEnergy]

/-- Every sphere has zero mass for the standard Gaussian on an `m × 1`
complex sample coordinate space. -/
theorem stdGaussian_oneColumn_sphere_zero {m : ℕ}
    (hm : 0 < m)
    (c : ComplexSample (m := m) (n := 1)) (R : ℝ) :
    stdGaussian (ComplexSample (m := m) (n := 1)) (Metric.sphere c R) = 0 := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  haveI : Nonempty ((Fin m × Fin 1) × Fin 2) := inferInstance
  haveI : Nontrivial (ComplexSample (m := m) (n := 1)) := inferInstance
  rw [stdGaussian_euclidean_eq_radialDensity]
  exact withDensity_absolutelyContinuous volume _
    (Measure.addHaar_sphere
      (volume : Measure (ComplexSample (m := m) (n := 1))) c R)

/-- The eigenvalue law of a noncentral complex Wishart matrix with one column
has no atoms, for every positive number of rows. -/
theorem oneColumnNoncentralEigenvalue_noAtom {m : ℕ} (hm : 0 < m)
    (M : Matrix (Fin m) (Fin 1) ℂ) (x : ℝ) :
    ((stdGaussian (ComplexSample (m := m) (n := 1))).map
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
      rw [oneColumnNoncentralEigenvalue_eq_shiftedNormSq hm]
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
    exact stdGaussian_oneColumn_sphere_zero hm _ _
  · have hevent :
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num)) ⁻¹' {x} =
          (∅ : Set (ComplexSample (m := m) (n := 1))) := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rw [oneColumnNoncentralEigenvalue_eq_shiftedNormSq hm]
      have hnonneg : 0 ≤ ‖z + complexSampleMean M‖ ^ 2 / 2 := by positivity
      exact ne_of_gt (lt_of_not_ge hx |>.trans_le hnonneg)
    rw [hevent]
    exact measure_empty

end JinWishart
