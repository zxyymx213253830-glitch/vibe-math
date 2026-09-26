import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory

namespace JinWishart

/-- The total `toSphere` measure on the unit sphere in three-dimensional
Euclidean space is `4π`. -/
theorem sphereThreeMeasure_univ :
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) Set.univ =
      ENNReal.ofReal (4 * Real.pi) := by
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hfinrank]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [← ENNReal.ofReal_natCast 3]
  norm_num only [Nat.cast_ofNat]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

end JinWishart
