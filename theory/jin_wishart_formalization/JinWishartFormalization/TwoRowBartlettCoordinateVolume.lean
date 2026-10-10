import JinWishartFormalization.TwoRowGramPositive
import JinWishartFormalization.GaussianRadialLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Bartlett coordinate volume bridge

Codex direction in the second local DeepSeek collaboration hour.
Reuse existing complex-coordinate volume and finite product equivalences;
do not redo radial integration or assume an actual Bartlett density.
[需人工审查] Volume normalization and correspondence with paper coordinates.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart
noncomputable section

def finFourNestedRealEquiv : GramChartSpace ≃ᵐ ℝ × (ℝ × (ℝ × ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
        ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)))

theorem finFourNestedRealEquiv_apply (q : GramChartSpace) :
    finFourNestedRealEquiv q = (q 0, (q 1, (q 2, q 3))) := by
  rfl

def twoRowBartlettCoordinateEquiv : (ℝ × (ℂ × ℝ)) ≃ᵐ GramChartSpace :=
  ((MeasurableEquiv.refl ℝ).prodCongr
    ((Complex.measurableEquivRealProd.prodCongr (MeasurableEquiv.refl ℝ)).trans
      MeasurableEquiv.prodAssoc)).trans finFourNestedRealEquiv.symm

theorem twoRowBartlettCoordinateEquiv_apply (p : ℝ × (ℂ × ℝ)) :
    twoRowBartlettCoordinateEquiv p = twoRowBartlettRealCoordinates p := by
  ext i
  fin_cases i <;> rfl

theorem volume_preserving_finFourNestedRealEquiv :
    MeasurePreserving finFourNestedRealEquiv := by
  have hi : MeasurePreserving (MeasurableEquiv.refl ℝ) := ⟨measurable_id, Measure.map_id⟩
  have h2 := volume_preserving_finTwoArrow ℝ
  have h3 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h4 := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  exact (hi.prod ((hi.prod h2).comp h3)).comp h4

theorem volume_preserving_twoRowBartlettCoordinateEquiv :
    MeasurePreserving twoRowBartlettCoordinateEquiv := by
  have hi : MeasurePreserving (MeasurableEquiv.refl ℝ) := ⟨measurable_id, Measure.map_id⟩
  have hc := Complex.volume_preserving_equiv_real_prod.prod hi
  have ha := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)).comp hc
  exact (MeasurePreserving.symm finFourNestedRealEquiv
    volume_preserving_finFourNestedRealEquiv).comp (hi.prod ha)

theorem measurable_twoRowBartlettRealCoordinates : Measurable twoRowBartlettRealCoordinates := by
  have he : (fun p => twoRowBartlettCoordinateEquiv p) = twoRowBartlettRealCoordinates :=
    funext twoRowBartlettCoordinateEquiv_apply
  rw [← he]
  exact twoRowBartlettCoordinateEquiv.measurable

theorem volume_preserving_twoRowBartlettRealCoordinates :
    MeasurePreserving twoRowBartlettRealCoordinates := by
  have he : (fun p => twoRowBartlettCoordinateEquiv p) = twoRowBartlettRealCoordinates :=
    funext twoRowBartlettCoordinateEquiv_apply
  rw [← he]
  exact volume_preserving_twoRowBartlettCoordinateEquiv

/-- Generic density transport; no assertion of an actual Gaussian density. -/
theorem twoRowBartlettCoordinate_density_transport
    (f : ℝ × (ℂ × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (volume.withDensity f).map twoRowBartlettRealCoordinates =
      volume.withDensity (f ∘ twoRowBartlettCoordinateEquiv.symm) := by
  have he : (fun p => twoRowBartlettCoordinateEquiv p) = twoRowBartlettRealCoordinates :=
    funext twoRowBartlettCoordinateEquiv_apply
  rw [← he]
  exact map_withDensity_measurePreserving twoRowBartlettCoordinateEquiv volume volume
    volume_preserving_twoRowBartlettCoordinateEquiv f hf

/-- Shared interface repair: the real gamma density and ENNReal density differ. -/
theorem measurable_gammaDensity_ennreal (a r : ℝ) : Measurable (gammaPDF a r) := by
  change Measurable (fun x => ENNReal.ofReal (gammaPDFReal a r x))
  exact (measurable_gammaPDFReal a r).ennreal_ofReal

end
end JinWishart

#print axioms JinWishart.volume_preserving_finFourNestedRealEquiv
#print axioms JinWishart.volume_preserving_twoRowBartlettCoordinateEquiv
#print axioms JinWishart.measurable_twoRowBartlettRealCoordinates
#print axioms JinWishart.volume_preserving_twoRowBartlettRealCoordinates
#print axioms JinWishart.twoRowBartlettCoordinate_density_transport
#print axioms JinWishart.measurable_gammaDensity_ennreal
