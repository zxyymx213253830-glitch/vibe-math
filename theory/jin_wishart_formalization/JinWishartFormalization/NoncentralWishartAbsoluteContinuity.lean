import JinWishartFormalization.CentralWishartAbsoluteContinuity

/-!
# Actual noncentral complex Wishart absolute continuity

Codex proofs. A finite-dimensional shifted Gaussian is dominated by the
unshifted Gaussian because both have a strictly positive Lebesgue density.
Pushforward preserves domination. Consequently the new central coordinate
absolute-continuity theorem extends to ANY deterministic complex mean when
columns <= rows. This is not an explicit noncentral density or spectral G2.
[需人工审查] Null-set transport, encoded mean, variance and model interpretation.
Existing rank-one noncentral trace/ncx2 controls are reused, not rerun.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem stdGaussian_shift_absolutelyContinuous {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => z + a) ≪
      stdGaussian (EuclideanSpace ℝ ι) := by
  have hshift : (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => z + a) ≪
      (volume : Measure (EuclideanSpace ℝ ι)) := by
    rw [stdGaussian_shift_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have hpos : (volume : Measure (EuclideanSpace ℝ ι)) ≪ stdGaussian (EuclideanSpace ℝ ι) := by
    rw [stdGaussian_euclidean_eq_radialDensity]
    apply withDensity_absolutelyContinuous'
    · fun_prop
    · apply ae_of_all
      intro x
      apply ne_of_gt
      apply ENNReal.ofReal_pos.mpr
      positivity
  exact hshift.trans hpos

/-- All rectangular shapes: the actual noncentral Gram is dominated by the
actual central Gram, including shapes where BOTH laws are singular. -/
theorem complexNoncentralWishart_absolutelyContinuous_central {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    complexNoncentralWishart M ≪ complexWishart (m := m) (n := n) := by
  have hlaw : complexNoncentralWishart M =
      ((stdGaussian (ComplexSample (m := m) (n := n))).map
        (fun z => z + complexSampleMean M)).map complexSampleGram := by
    rw [Measure.map_map measurable_complexSampleGram (by fun_prop)]
    unfold complexNoncentralWishart
    congr 1
    funext z
    simp only [Function.comp_def, complexSampleGram, complexSampleMatrix_add_mean]
  rw [hlaw]
  exact (stdGaussian_shift_absolutelyContinuous (complexSampleMean M)).map measurable_complexSampleGram

/-- Full-dimensional noncentral Hermitian coordinate domination for s<=t. -/
theorem complexNoncentralWishart_realCoordinates_absolutelyContinuous {t s : ℕ}
    (M : Matrix (Fin t) (Fin s) ℂ) (hst : s ≤ t) :
    (complexNoncentralWishart M).map realCoordinatesOfHermitian ≪
      hermitianRealCoordinateMeasure s := by
  exact ((complexNoncentralWishart_absolutelyContinuous_central M).map
    continuous_realCoordinatesOfHermitian.measurable).trans
      (complexWishart_realCoordinates_absolutelyContinuous_of_le t s hst)

end
end JinWishart

#print axioms JinWishart.stdGaussian_shift_absolutelyContinuous
#print axioms JinWishart.complexNoncentralWishart_absolutelyContinuous_central
#print axioms JinWishart.complexNoncentralWishart_realCoordinates_absolutelyContinuous
