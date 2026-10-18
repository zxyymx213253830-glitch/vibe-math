import JinWishartFormalization.CentralWishartMinimum
import JinWishartFormalization.CentralWishartMatrixDensity

/-!
# Matrix-level memorylessness of the actual central square Wishart law

Codex. This is a whole-matrix restricted pushforward identity, stronger than
the scalar minimum tail. It is unnormalized: mass exp(-n*x) is retained.
[需人工审查] Canonical Haar translation, restrictions and conditional interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem centralWishartSquareDensity_shift (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (q : Matrix (Fin n) (Fin n) ℝ) (hq : q ∈ centralCoordinatePositiveCone n) :
    centralWishartCoordinateDensity 0 n (q + x • 1) =
      ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) * centralWishartCoordinateDensity 0 n q := by
  have hs : q + x • 1 ∈ centralCoordinateShiftedCone n x := by
    change (hermitianOfRealCoordinates (q + x • 1) - (x : ℂ) • 1).PosDef
    rw [hermitianOfRealCoordinates_shift, add_sub_cancel_right]
    exact hq
  rw [centralWishartCoordinateDensity_on_cone 0 n _
      (centralCoordinateShiftedCone_subset_positive n x hx hs),
    centralWishartCoordinateDensity_on_cone 0 n q hq,
    hermitianOfRealCoordinates_shift, centralConeWeight_square_shift,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
  ring

theorem centralWishartSquareDensity_shift_indicator (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (q : Matrix (Fin n) (Fin n) ℝ) :
    (centralCoordinateShiftedCone n x).indicator (centralWishartCoordinateDensity 0 n)
      (q + x • 1) = ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) *
        centralWishartCoordinateDensity 0 n q := by
  classical
  have he : q + x • 1 ∈ centralCoordinateShiftedCone n x ↔ q ∈ centralCoordinatePositiveCone n := by
    change (hermitianOfRealCoordinates (q + x • 1) - (x : ℂ) • 1).PosDef ↔ _
    rw [hermitianOfRealCoordinates_shift, add_sub_cancel_right]
    rfl
  by_cases hq : q ∈ centralCoordinatePositiveCone n
  · rw [Set.indicator_of_mem (he.mpr hq), centralWishartSquareDensity_shift n x hx q hq]
  · rw [Set.indicator_of_notMem (not_iff_not.mpr he |>.mpr hq)]
    change 0 = _ * centralWishartCoordinateDensity 0 n q
    have hd : centralWishartCoordinateDensity 0 n q = 0 := if_neg hq
    rw [hd, mul_zero]

/-- Whole actual matrix law restricted to W>xI is a translated copy times its mass. -/
theorem actualCentralSquare_coordinate_restrict_eq_shift (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian).restrict
      (centralCoordinateShiftedCone n x)) =
      ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) •
        (((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian).map
          (fun q : Matrix (Fin n) (Fin n) ℝ => q + x • 1)) := by
  let e := MeasurableEquiv.addRight (x • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hm := measurable_centralWishartCoordinateDensity 0 n
  have hmp : MeasurePreserving e (hermitianRealCoordinateMeasure n)
      (hermitianRealCoordinateMeasure n) := measurePreserving_add_right _ _
  have hd := complexWishart_realCoordinates_eq_closedDensity 0 n
  simp only [Nat.zero_add] at hd
  rw [hd]
  rw [restrict_withDensity (measurableSet_centralCoordinateShiftedCone n x),
    ← withDensity_indicator (measurableSet_centralCoordinateShiftedCone n x)]
  change _ = ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) •
    ((hermitianRealCoordinateMeasure n).withDensity (centralWishartCoordinateDensity 0 n)).map e
  rw [map_withDensity_measurePreserving e _ _ hmp _ hm,
    ← withDensity_smul _ (hm.comp e.symm.measurable)]
  congr 1
  funext q
  have h := centralWishartSquareDensity_shift_indicator n x hx (e.symm q)
  have he : e.symm q + x • 1 = q := e.apply_symm_apply q
  rw [he] at h
  exact h

/-- Subtracting xI under the strict-cone event recovers the full actual law,
times event mass. Dividing by that positive mass gives the conditional law. -/
theorem actualCentralSquare_coordinate_residual_law (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ((((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian).restrict
      (centralCoordinateShiftedCone n x)).map
        (fun q : Matrix (Fin n) (Fin n) ℝ => q - x • 1)) =
      ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) •
        ((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian) := by
  rw [actualCentralSquare_coordinate_restrict_eq_shift n x hx, Measure.map_smul,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun q : Matrix (Fin n) (Fin n) ℝ => q - x • 1) ∘
      (fun q => q + x • 1) = id := by
    funext q
    exact add_sub_cancel_right q (x • 1)
  rw [he, Measure.map_id]
  fun_prop

theorem actualCentralSquare_coordinate_conditional_residual_law (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (ENNReal.ofReal (Real.exp (-(n : ℝ) * x)))⁻¹ •
      ((((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian).restrict
        (centralCoordinateShiftedCone n x)).map
          (fun q : Matrix (Fin n) (Fin n) ℝ => q - x • 1)) =
      ((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian) := by
  rw [actualCentralSquare_coordinate_residual_law n x hx, smul_smul,
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
      ENNReal.ofReal_ne_top, one_smul]

/-- Whole actual complex-matrix residual law under W>xI. -/
theorem actualCentralSquare_matrix_residual_law (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ((complexWishart (m := n) (n := n)).restrict
      {A | (A - (x : ℂ) • 1).PosDef}).map
        (fun A : Matrix (Fin n) (Fin n) ℂ => A - (x : ℂ) • 1) =
      ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) • complexWishart (m := n) (n := n) := by
  have hH := continuous_hermitianOfRealCoordinates (n := n) |>.measurable
  have hs : MeasurableSet {A : Matrix (Fin n) (Fin n) ℂ | (A - (x : ℂ) • 1).PosDef} :=
    (measurableSet_complex_posDef n).preimage (by fun_prop)
  have hcomp : (fun A : Matrix (Fin n) (Fin n) ℂ => A - (x : ℂ) • 1) ∘
      hermitianOfRealCoordinates = hermitianOfRealCoordinates ∘
        (fun q : Matrix (Fin n) (Fin n) ℝ => q - x • 1) := by
    funext q
    change _ = hermitianOfRealCoordinates (q - x • 1)
    rw [sub_eq_add_neg, ← neg_smul, hermitianOfRealCoordinates_shift]
    simp [sub_eq_add_neg]
  calc
    _ = ((((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian).restrict
        (centralCoordinateShiftedCone n x)).map
          (fun q : Matrix (Fin n) (Fin n) ℝ => q - x • 1)).map hermitianOfRealCoordinates := by
      conv_lhs => rw [complexWishart_eq_realCoordinates_map n n]
      rw [Measure.restrict_map hH hs, Measure.map_map (by fun_prop) hH,
        Measure.map_map hH (by fun_prop), hcomp]
      rfl
    _ = (ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) •
        ((complexWishart (m := n) (n := n)).map realCoordinatesOfHermitian)).map
          hermitianOfRealCoordinates := by rw [actualCentralSquare_coordinate_residual_law n x hx]
    _ = _ := by
      rw [Measure.map_smul, ← complexWishart_eq_realCoordinates_map n n]
      exact hH.aemeasurable

end
end JinWishart

#print axioms JinWishart.centralWishartSquareDensity_shift
#print axioms JinWishart.centralWishartSquareDensity_shift_indicator
#print axioms JinWishart.actualCentralSquare_coordinate_restrict_eq_shift
#print axioms JinWishart.actualCentralSquare_coordinate_residual_law
#print axioms JinWishart.actualCentralSquare_coordinate_conditional_residual_law
#print axioms JinWishart.actualCentralSquare_matrix_residual_law
