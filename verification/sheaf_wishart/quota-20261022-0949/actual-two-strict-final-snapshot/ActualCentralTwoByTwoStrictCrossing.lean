import JinWishartFormalization.CentralTwoByTwoMaximumClosedCDF
import JinWishartFormalization.OrderedEigenvalueStrictRecurrence

/-! Actual central properCN1 2x2 strict crossing. Measure/model steps require human review. -/
open MeasureTheory Set ProbabilityTheory
namespace JinWishart
noncomputable section

theorem actualCentralTwoByTwo_coordinate_atoms_zero (x : ℝ) :
    (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1=x}=0 ∧
    (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).2=x}=0 := by
  have hv : (volume : Measure (ℝ × ℝ)) {y | y.1=x}=0 := by
    have hs : {y : ℝ × ℝ | y.1=x}=({x} : Set ℝ) ×ˢ univ := by ext y;simp
    rw [hs,Measure.volume_eq_prod,Measure.prod_prod]
    simp
  have hh : (volume : Measure (ℝ × ℝ)) {y | y.2=x}=0 := by
    have hs : {y : ℝ × ℝ | y.2=x}=univ ×ˢ ({x} : Set ℝ) := by ext y;simp
    rw [hs,Measure.volume_eq_prod,Measure.prod_prod]
    simp
  have hV := withDensity_absolutelyContinuous (volume : Measure (ℝ × ℝ))
    centralTwoByTwoPaperEigenvalueDensity hv
  have hH := withDensity_absolutelyContinuous (volume : Measure (ℝ × ℝ))
    centralTwoByTwoPaperEigenvalueDensity hh
  rw [← actualCentralTwoByTwo_jointEigenvalueDensity,centralTwoByTwoJointEigenvalueLaw,
    Measure.map_apply measurable_centralTwoByTwoEigenpair
      (measurableSet_eq_fun measurable_fst measurable_const)] at hV
  rw [← actualCentralTwoByTwo_jointEigenvalueDensity,centralTwoByTwoJointEigenvalueLaw,
    Measure.map_apply measurable_centralTwoByTwoEigenpair
      (measurableSet_eq_fun measurable_snd measurable_const)] at hH
  exact ⟨hV,hH⟩

theorem actualCentralTwoByTwo_strict_CDF_recurrence (x : ℝ) :
    (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).2≤x}=
      (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1≤x}+
        centralTwoByTwoT3Increment x := by
  apply orderedPair_sublevelMass_eq_add_strict _
    (fun z => (centralTwoByTwoEigenpair z).2) (fun z => (centralTwoByTwoEigenpair z).1)
    (measurable_snd.comp measurable_centralTwoByTwoEigenpair)
    (measurable_fst.comp measurable_centralTwoByTwoEigenpair) x
  · intro z
    rw [centralTwoByTwoEigenpair_eq_traceSpectralPair]
    generalize twoRowTraceCoordinates (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))) = p
    change p 0-‖(WithLp.toLp 2 ![p 1,p 2,p 3] : EuclideanSpace ℝ (Fin 3))‖ ≤
      p 0+‖(WithLp.toLp 2 ![p 1,p 2,p 3] : EuclideanSpace ℝ (Fin 3))‖
    linarith [norm_nonneg (WithLp.toLp 2 ![p 1,p 2,p 3] : EuclideanSpace ℝ (Fin 3))]
  · exact (actualCentralTwoByTwo_coordinate_atoms_zero x).2

theorem actualCentralTwoByTwo_T3Increment_closed (x : ℝ) (hx : 0≤x) :
    (centralTwoByTwoT3Increment x).toReal=
      (x^2+2)*Real.exp (-x)-2*Real.exp (-2*x) := by
  have h := congrArg ENNReal.toReal (actualCentralTwoByTwo_strict_CDF_recurrence x)
  have hi : centralTwoByTwoT3Increment x ≠ ⊤ := measure_ne_top _ _
  rw [ENNReal.toReal_add (measure_ne_top _ _) hi] at h
  have hmin : ((stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | (centralTwoByTwoEigenpair z).2≤x}).toReal=1-Real.exp (-2*x) := by
    simpa only [centralTwoByTwoEigenpair,twoRowActualMinimum] using actualTwoRow_minimum_CDF x hx
  rw [hmin,actualCentralTwoByTwo_maximum_CDF x hx] at h
  linarith
end
end JinWishart
#print axioms JinWishart.actualCentralTwoByTwo_coordinate_atoms_zero
#print axioms JinWishart.actualCentralTwoByTwo_strict_CDF_recurrence
#print axioms JinWishart.actualCentralTwoByTwo_T3Increment_closed

