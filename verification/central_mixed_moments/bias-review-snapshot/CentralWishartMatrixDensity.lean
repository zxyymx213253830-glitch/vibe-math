import JinWishartFormalization.CentralWishartNormalization

/-!
# Matrix-valued form of the actual central Wishart density

Codex. The reference is the pushforward of canonical n^2 real coordinate
Lebesgue measure to Hermitian matrices inside all complex matrices. It is NOT
ambient complex Lebesgue measure restricted to the Hermitian locus.
[需人工审查] Reference measure and actual-model interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

def hermitianAmbientCoordinateMeasure (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  (hermitianRealCoordinateMeasure n).map hermitianOfRealCoordinates

def centralWishartMatrixDensity (d n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ := by
  classical
  exact if A.PosDef then ENNReal.ofReal
    (centralWishartDensityConstant d n * A.det.re ^ d * Real.exp (-A.trace.re)) else 0

theorem measurable_centralWishartMatrixDensity (d n : ℕ) :
    Measurable (centralWishartMatrixDensity d n) := by
  classical
  unfold centralWishartMatrixDensity
  refine Measurable.ite (measurableSet_complex_posDef n) ?_ measurable_const
  apply ENNReal.measurable_ofReal.comp
  exact (show Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
    centralWishartDensityConstant d n * A.det.re ^ d * Real.exp (-A.trace.re)) by fun_prop).measurable

theorem complexWishart_eq_realCoordinates_map (m n : ℕ) :
    complexWishart (m := m) (n := n) =
      ((complexWishart (m := m) (n := n)).map realCoordinatesOfHermitian).map
        hermitianOfRealCoordinates := by
  rw [Measure.map_map continuous_hermitianOfRealCoordinates.measurable
    continuous_realCoordinatesOfHermitian.measurable]
  have hp : ∀ᵐ A ∂complexWishart (m := m) (n := n), A.PosSemidef :=
    (mem_ae_iff_prob_eq_one Matrix.posSemidef_is_closed.measurableSet).mpr
      complexWishart_measure_posSemidef
  have he : (complexWishart (m := m) (n := n)).map
      (hermitianOfRealCoordinates ∘ realCoordinatesOfHermitian) =
      (complexWishart (m := m) (n := n)).map id := by
    apply Measure.map_congr
    filter_upwards [hp] with A hA
    exact hermitianOfRealCoordinates_realCoordinates A hA.isHermitian
  rw [he, Measure.map_id]

/-- The ACTUAL matrix law, rather than only its coordinate pushforward. -/
theorem complexWishart_eq_map_closedDensity (d n : ℕ) :
    complexWishart (m := d + n) (n := n) =
      ((hermitianRealCoordinateMeasure n).withDensity
        (centralWishartCoordinateDensity d n)).map hermitianOfRealCoordinates := by
  rw [← complexWishart_realCoordinates_eq_closedDensity]
  exact complexWishart_eq_realCoordinates_map (d + n) n

/-- A density on complex matrices relative to the explicit Hermitian coordinate
measure. No false ambient 2n^2-dimensional volume statement is made. -/
theorem complexWishart_eq_matrixDensity (d n : ℕ) :
    complexWishart (m := d + n) (n := n) =
      (hermitianAmbientCoordinateMeasure n).withDensity (centralWishartMatrixDensity d n) := by
  rw [complexWishart_eq_map_closedDensity]
  ext s hs
  have hH := continuous_hermitianOfRealCoordinates (n := n) |>.measurable
  rw [Measure.map_apply hH hs, withDensity_apply _ (hs.preimage hH), withDensity_apply _ hs]
  exact (setLIntegral_map hs (measurable_centralWishartMatrixDensity d n) hH).symm

end
end JinWishart

#print axioms JinWishart.measurable_centralWishartMatrixDensity
#print axioms JinWishart.complexWishart_eq_realCoordinates_map
#print axioms JinWishart.complexWishart_eq_map_closedDensity
#print axioms JinWishart.complexWishart_eq_matrixDensity
