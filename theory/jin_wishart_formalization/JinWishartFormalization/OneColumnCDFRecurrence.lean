import JinWishartFormalization.OneColumnNoAtom
import JinWishartFormalization.OrderedEigenvalueCDFRecurrence
import Mathlib.Probability.CDF

/-!
# The one-column endpoint of the ordered-eigenvalue CDF recurrence

When `n = 1`, there is only one ordered Gram eigenvalue.  The pair recurrence
therefore degenerates to its one-statistic endpoint; atomlessness identifies
the weak (`≤`) CDF event with its strict (`<`) version.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

variable {m : ℕ}

noncomputable section

/-- The abstract ordered-pair recurrence instantiated by the sole ordered
eigenvalue in the one-column Wishart model.  Since there is no adjacent
eigenvalue when `n = 1`, the two ordered statistics coincide. -/
theorem oneColumn_orderedEigenvalue_pairRecurrence
    (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ) (x : ℝ) :
    (stdGaussian (ComplexSample (m := m) (n := 1)))
        {z | complexNoncentralSampleSmallestEigenvalue M (by norm_num) z ≤ x} =
      (stdGaussian (ComplexSample (m := m) (n := 1)))
          {z | complexNoncentralSampleSmallestEigenvalue M (by norm_num) z ≤ x} +
        (stdGaussian (ComplexSample (m := m) (n := 1)))
          {z | complexNoncentralSampleSmallestEigenvalue M (by norm_num) z ≤ x ∧
            x < complexNoncentralSampleSmallestEigenvalue M (by norm_num) z} := by
  let stat : ComplexSample (m := m) (n := 1) → ℝ :=
    complexNoncentralSampleSmallestEigenvalue M (by norm_num)
  have hstat : Measurable stat := by
    dsimp [stat]
    exact measurable_complexNoncentralSampleSmallestEigenvalue M (by norm_num)
  have hrec := orderedPair_sublevelMass_eq_add
    (stdGaussian (ComplexSample (m := m) (n := 1))) stat stat hstat hstat x
    (fun _ => le_rfl)
  simpa [stat] using hrec

/-- The actual pushforward law of the one-column noncentral Wishart eigenvalue
has the same mass on `Iic x` and `Iio x`, by the no-atom theorem. -/
theorem oneColumnNoncentralEigenvalue_weakSublevel_eq_strict
    (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ) (x : ℝ) :
    ((stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) (Iic x) =
    ((stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) (Iio x) := by
  let ν : Measure ℝ :=
    (stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))
  have hset : Iic x = Iio x ∪ {x} := by
    ext y
    simp [le_iff_lt_or_eq]
  rw [hset, measure_union (by grind) (measurableSet_singleton x)]
  rw [oneColumnNoncentralEigenvalue_noAtom hm M x]
  simp [ν]

/-- The CDF of the actual one-column noncentral Wishart ordered eigenvalue is
the strict-sublevel probability.  This is the atomless endpoint needed when
specializing ordered-event recurrences to `n = 1`. -/
theorem oneColumnNoncentralCDF_eq_strictSublevelMass
    (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      (((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))).real (Iio x)) := by
  let ν : Measure ℝ :=
    (stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))
  have hset : Iic x = Iio x ∪ {x} := by
    ext y
    simp [le_iff_lt_or_eq]
  rw [cdf_eq_real, measureReal_def, hset,
    measure_union (by grind) (measurableSet_singleton x)]
  rw [oneColumnNoncentralEigenvalue_noAtom hm M x]
  simp [measureReal_def]

end

end JinWishart
