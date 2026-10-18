import JinWishartFormalization.GaussianBartlettGramRecursion
import JinWishartFormalization.CentralHermitianCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Dimension-independent fixed-pivot Bartlett fiber volume

Codex proofs. For r>0, scale the n complex off-diagonal row coefficients by
sqrt(r), and translate the n^2 explicit real residual coordinates by coords(zᴴz).
Haar scaling and skew_product give inverse volume factor r^(-n), without a
dimension-by-dimension derivative calculation. This is a Lebesgue fiber theorem,
not yet an actual general Wishart density or a full Hermitian block-volume map.
[需人工审查] Product Haar normalization, skew-product, and later coordinate alignment.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def centralBartlettResidualShift {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := realCoordinatesOfHermitian (complexVectorGramRankOne z)

theorem continuous_centralBartlettResidualShift (n : ℕ) :
    Continuous (centralBartlettResidualShift (n := n)) := by
  apply continuous_realCoordinatesOfHermitian.comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : EuclideanSpace ℂ (Fin n) => star (z i) * z j)
  fun_prop

def centralBartlettVolumeFiber {n : ℕ} (r : ℝ)
    (p : EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ :=
  ((Real.sqrt r) • p.1, p.2 + centralBartlettResidualShift p.1)

theorem continuous_centralBartlettVolumeFiber (n : ℕ) (r : ℝ) :
    Continuous (centralBartlettVolumeFiber (n := n) r) := by
  exact (continuous_fst.const_smul (Real.sqrt r)).prodMk
    (continuous_snd.add ((continuous_centralBartlettResidualShift n).comp continuous_fst))

def centralBartlettVolumeFiberEquiv (n : ℕ) (r : ℝ) (hr : 0 < r) :
    (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) ≃ᵐ
      (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) where
  toFun := centralBartlettVolumeFiber r
  invFun p := ((Real.sqrt r)⁻¹ • p.1,
    p.2 - centralBartlettResidualShift ((Real.sqrt r)⁻¹ • p.1))
  left_inv := by
    intro p
    simp [centralBartlettVolumeFiber, smul_smul, ne_of_gt (Real.sqrt_pos.2 hr)]
  right_inv := by
    intro p
    simp [centralBartlettVolumeFiber, smul_smul, ne_of_gt (Real.sqrt_pos.2 hr)]
  measurable_toFun := (continuous_centralBartlettVolumeFiber n r).measurable
  measurable_invFun := ((continuous_fst.const_smul ((Real.sqrt r)⁻¹)).prodMk
    (continuous_snd.sub ((continuous_centralBartlettResidualShift n).comp
      (continuous_fst.const_smul ((Real.sqrt r)⁻¹))))).measurable

instance sigmaFinite_hermitianRealCoordinateMeasure (n : ℕ) :
    SigmaFinite (hermitianRealCoordinateMeasure n) :=
  inferInstanceAs (SigmaFinite (volume : Measure (Fin n → Fin n → ℝ)))

instance isAddRightInvariant_hermitianRealCoordinateMeasure (n : ℕ) :
    (hermitianRealCoordinateMeasure n).IsAddRightInvariant :=
  inferInstanceAs ((volume : Measure (Fin n → Fin n → ℝ)).IsAddRightInvariant)

/-- Complex dimension n means real dimension 2n; the inverse scaling is r^-n. -/
theorem centralBartlett_sqrt_scale_volume (n : ℕ) (r : ℝ) (hr : 0 < r) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).map (fun z => (Real.sqrt r) • z) =
      ENNReal.ofReal ((r ^ n)⁻¹) • (volume : Measure (EuclideanSpace ℂ (Fin n))) := by
  rw [Measure.map_addHaar_smul volume (ne_of_gt (Real.sqrt_pos.2 hr)),
    finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hp : (Real.sqrt r) ^ (2 * n) = r ^ n := by
    rw [pow_mul, Real.sq_sqrt hr.le]
  rw [hp, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le n))]

/-- Actual coordinate volume transport for each fixed positive pivot. -/
theorem centralBartlettVolumeFiber_map_volume (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod
      (hermitianRealCoordinateMeasure n)).map (centralBartlettVolumeFiber r) =
      ENNReal.ofReal ((r ^ n)⁻¹) • ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod
        (hermitianRealCoordinateMeasure n)) := by
  have hf : MeasurePreserving (fun z : EuclideanSpace ℂ (Fin n) => (Real.sqrt r) • z)
      volume (ENNReal.ofReal ((r ^ n)⁻¹) • volume) :=
    ⟨by fun_prop, centralBartlett_sqrt_scale_volume n r hr⟩
  have hg : Measurable (fun p : EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ =>
      p.2 + centralBartlettResidualShift p.1) :=
    (continuous_snd.add ((continuous_centralBartlettResidualShift n).comp continuous_fst)).measurable
  have hfiber : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℂ (Fin n))),
      (hermitianRealCoordinateMeasure n).map
        (fun Q => Q + centralBartlettResidualShift z) = hermitianRealCoordinateMeasure n :=
    ae_of_all _ (fun z => (measurePreserving_add_right (hermitianRealCoordinateMeasure n)
      (centralBartlettResidualShift z)).map_eq)
  exact (hf.skew_product hg hfiber).map_eq.trans (Measure.prod_smul_left _)

/-- Generic Lebesgue density transport across the fixed-pivot fiber. This
does not assume that an actual Wishart measure already has a density. -/
theorem centralBartlettVolumeFiber_density_map (n : ℕ) (r : ℝ) (hr : 0 < r)
    (f : EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (((volume : Measure (EuclideanSpace ℂ (Fin n))).prod
      (hermitianRealCoordinateMeasure n)).withDensity f).map (centralBartlettVolumeFiber r) =
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod
        (hermitianRealCoordinateMeasure n)).withDensity
          (fun p => ENNReal.ofReal ((r ^ n)⁻¹) * f ((centralBartlettVolumeFiberEquiv n r hr).symm p)) := by
  let e := centralBartlettVolumeFiberEquiv n r hr
  let μ := (volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n)
  have hmp : MeasurePreserving e μ (ENNReal.ofReal ((r ^ n)⁻¹) • μ) :=
    ⟨e.measurable, centralBartlettVolumeFiber_map_volume n r hr⟩
  have h := map_withDensity_measurePreserving e μ (ENNReal.ofReal ((r ^ n)⁻¹) • μ) hmp f hf
  rw [withDensity_smul_measure] at h
  exact h.trans (withDensity_smul _ (hf.comp e.symm.measurable)).symm

theorem realCoordinatesOfHermitian_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    realCoordinatesOfHermitian (A + B) =
      realCoordinatesOfHermitian A + realCoordinatesOfHermitian B := by
  ext i j
  by_cases hij : i ≤ j <;>
    simp [realCoordinatesOfHermitian, hij, Matrix.add_apply, add_comm]

/-- The translated real residual coordinates agree with the lower Gram block. -/
theorem centralBartlettResidualShift_coordinates {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    realCoordinatesOfHermitian (hermitianOfRealCoordinates Q + complexVectorGramRankOne z) =
      Q + centralBartlettResidualShift z := by
  rw [realCoordinatesOfHermitian_add, realCoordinates_hermitianOfRealCoordinates]
  rfl

end
end JinWishart

#print axioms JinWishart.continuous_centralBartlettResidualShift
#print axioms JinWishart.continuous_centralBartlettVolumeFiber
#print axioms JinWishart.sigmaFinite_hermitianRealCoordinateMeasure
#print axioms JinWishart.isAddRightInvariant_hermitianRealCoordinateMeasure
#print axioms JinWishart.centralBartlett_sqrt_scale_volume
#print axioms JinWishart.centralBartlettVolumeFiber_map_volume
#print axioms JinWishart.centralBartlettVolumeFiber_density_map
#print axioms JinWishart.realCoordinatesOfHermitian_add
#print axioms JinWishart.centralBartlettResidualShift_coordinates
