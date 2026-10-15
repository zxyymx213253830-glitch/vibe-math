import JinWishartFormalization.CentralHermitianCoordinates
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Central cone translation on the explicitly chosen n^2 real coordinates

This proves an identity of candidate-kernel integrals, not an actual Wishart
probability formula. No target density is assumed as a hypothesis. The missing
step is still to derive that density from the actual Gaussian Gram model.
[需人工审查] Coordinate volume, eventual density normalization and paper use.
-/

open Matrix MeasureTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

def centralCoordinatePositiveCone (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {q | (hermitianOfRealCoordinates q).PosDef}

def centralCoordinateShiftedCone (n : ℕ) (x : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {q | (hermitianOfRealCoordinates q - (x : ℂ) • 1).PosDef}

theorem centralCoordinateShiftedCone_eq_image (n : ℕ) (x : ℝ) :
    centralCoordinateShiftedCone n x =
      (fun q : Matrix (Fin n) (Fin n) ℝ => q + x • 1) '' centralCoordinatePositiveCone n := by
  ext q
  constructor
  · intro hq
    refine ⟨q + (-x) • 1, ?_, ?_⟩
    · change (hermitianOfRealCoordinates (q + (-x) • 1)).PosDef
      rw [hermitianOfRealCoordinates_shift]
      simpa [centralCoordinateShiftedCone, neg_smul, sub_eq_add_neg] using hq
    · rw [neg_smul]
      abel
  · rintro ⟨p, hp, rfl⟩
    change (hermitianOfRealCoordinates (p + x • 1) - (x : ℂ) • 1).PosDef
    rw [hermitianOfRealCoordinates_shift, add_sub_cancel_right]
    exact hp

/-- General central-route integral formula, with the determinant term retained.
The measure is product Lebesgue on n^2 real coordinates, not ambient complex volume. -/
theorem centralCone_candidateIntegral_shift (n degree : ℕ) (x : ℝ) :
    (∫⁻ q in centralCoordinateShiftedCone n x,
      ENNReal.ofReal (centralConeWeight degree (hermitianOfRealCoordinates q))
        ∂hermitianRealCoordinateMeasure n) =
      ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) *
        (∫⁻ p in centralCoordinatePositiveCone n,
          ENNReal.ofReal ((hermitianOfRealCoordinates p + (x : ℂ) • 1).det.re ^ degree *
            Real.exp (-(hermitianOfRealCoordinates p).trace.re))
              ∂hermitianRealCoordinateMeasure n) := by
  letI : (hermitianRealCoordinateMeasure n).IsAddRightInvariant := by
    unfold hermitianRealCoordinateMeasure
    exact Measure.pi.isAddRightInvariant _
  have hc := (measurePreserving_add_right (hermitianRealCoordinateMeasure n)
      (x • (1 : Matrix (Fin n) (Fin n) ℝ))).setLIntegral_comp_emb
    (MeasurableEquiv.addRight (x • (1 : Matrix (Fin n) (Fin n) ℝ))).measurableEmbedding
    (fun q => ENNReal.ofReal (centralConeWeight degree (hermitianOfRealCoordinates q)))
    (centralCoordinatePositiveCone n)
  rw [centralCoordinateShiftedCone_eq_image]
  rw [← hc]
  simp_rw [hermitianOfRealCoordinates_shift, centralConeWeight_shift, mul_assoc,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The square-case kernel integral factors, but its actual-model mass is not assumed. -/
theorem centralCone_square_candidateIntegral_shift (n : ℕ) (x : ℝ) :
    (∫⁻ q in centralCoordinateShiftedCone n x,
      ENNReal.ofReal (centralConeWeight 0 (hermitianOfRealCoordinates q))
        ∂hermitianRealCoordinateMeasure n) =
      ENNReal.ofReal (Real.exp (-(n : ℝ) * x)) *
        (∫⁻ p in centralCoordinatePositiveCone n,
          ENNReal.ofReal (centralConeWeight 0 (hermitianOfRealCoordinates p))
            ∂hermitianRealCoordinateMeasure n) := by
  simpa only [pow_zero, one_mul, centralConeWeight] using
    centralCone_candidateIntegral_shift n 0 x

end
end JinWishart

#print axioms JinWishart.centralCoordinateShiftedCone_eq_image
#print axioms JinWishart.centralCone_candidateIntegral_shift
#print axioms JinWishart.centralCone_square_candidateIntegral_shift
