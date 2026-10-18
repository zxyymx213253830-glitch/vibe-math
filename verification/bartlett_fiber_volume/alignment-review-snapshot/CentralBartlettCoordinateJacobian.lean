import JinWishartFormalization.HermitianBlockCoordinates
import JinWishartFormalization.CentralBartlettVolumeTransport
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# General Bartlett weighted volume map in canonical Hermitian coordinates

Codex proofs. The mixed positive-pivot map is aligned with the explicit
(n+1)^2-real-coordinate measure by a volume-preserving equivalence. The
forward weight is r^n. This is a general change-of-volume theorem, not yet
the actual Wishart density induction or a spectral Jacobian.
[需人工审查] Measure restriction, coordinate normalization and later model use.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def centralBartlettCoordinateChart {n : ℕ}
    (p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (hermitianBlockCoordinateEquiv n).symm (centralBartlettVolumeMap p)

theorem hermitianBlockCoordinateEquiv_gram (n : ℕ) (r : ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) :
    hermitianBlockCoordinateEquiv n
      (realCoordinatesOfHermitian (centralBartlettGram r z (hermitianOfRealCoordinates Q))) =
        centralBartlettVolumeMap (r, (z, Q)) := by
  rw [hermitianBlockCoordinateEquiv_apply]
  apply Prod.ext
  · simp [realCoordinatesOfHermitian, centralBartlettGram, centralBartlettVolumeMap]
  · apply Prod.ext
    · ext j
      apply Complex.ext <;>
        simp [centralBartlettVolumeMap, centralBartlettVolumeFiber, realCoordinatesOfHermitian,
          centralBartlettGram, Complex.real_smul, mul_comm]
    · have h := centralBartlettResidualShift_coordinates Q z
      ext i j
      have hij := congrArg (fun M => M i j) h
      simpa [realCoordinatesOfHermitian, centralBartlettGram, complexVectorGramRankOne,
        centralBartlettVolumeMap, centralBartlettVolumeFiber, Matrix.add_apply] using hij

theorem centralBartlettCoordinateChart_eq_realGram (n : ℕ) (r : ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) :
    centralBartlettCoordinateChart (r, (z, Q)) =
      realCoordinatesOfHermitian (centralBartlettGram r z (hermitianOfRealCoordinates Q)) := by
  apply (hermitianBlockCoordinateEquiv n).injective
  rw [centralBartlettCoordinateChart, MeasurableEquiv.apply_symm_apply,
    hermitianBlockCoordinateEquiv_gram]

/-- The actual canonical real-coordinate volume formula, every n including 0. -/
theorem centralBartlettCoordinateChart_weighted_volume (n : ℕ) :
    ((((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n))).withDensity
        (fun p => ENNReal.ofReal (p.1 ^ n))).map centralBartlettCoordinateChart =
      (hermitianRealCoordinateMeasure (n + 1)).restrict
        {q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | 0 < q 0 0} := by
  let ν := (volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n)
  let e := hermitianBlockCoordinateEquiv n
  have hs : MeasurableSet {p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) |
      0 < p.1} := measurableSet_lt measurable_const measurable_fst
  have hpre : e ⁻¹' {p | 0 < p.1} = {q | 0 < q 0 0} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, e, hermitianBlockCoordinateEquiv_apply]
  have hp := (hermitianBlockCoordinateEquiv_measurePreserving n).restrict_preimage hs
  change MeasurePreserving e _ _ at hp
  rw [hpre] at hp
  have hi := MeasurePreserving.symm e hp
  have hrestrict : ((volume : Measure ℝ).prod ν).restrict {p | 0 < p.1} =
      ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ν := by
    rw [show {p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) | 0 < p.1} =
      Set.Ioi 0 ×ˢ Set.univ by ext p; simp]
    exact (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ)) (ν := ν) (Set.Ioi 0)).symm
  rw [hrestrict] at hi
  change Measure.map ((e.symm : _ → _) ∘ centralBartlettVolumeMap) _ = _
  rw [← Measure.map_map e.symm.measurable (continuous_centralBartlettVolumeMap n).measurable,
    centralBartlettVolumeMap_weighted_volume]
  exact hi.map_eq

end
end JinWishart

#print axioms JinWishart.hermitianBlockCoordinateEquiv_gram
#print axioms JinWishart.centralBartlettCoordinateChart_eq_realGram
#print axioms JinWishart.centralBartlettCoordinateChart_weighted_volume
