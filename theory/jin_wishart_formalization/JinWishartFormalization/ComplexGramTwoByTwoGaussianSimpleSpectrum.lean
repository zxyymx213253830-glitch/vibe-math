import JinWishartFormalization.ComplexGramTwoByTwoDiscriminantNull
import JinWishartFormalization.GaussianRadialLaw
import JinWishartFormalization.WishartProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Almost-sure simple spectrum for the shifted complex `2 × 2` Gram sample

This file is intentionally limited to the complex `2 × 2` case.  It transfers
the polynomial discriminant null set to arbitrary shifted complex Gaussian
samples by a finite coordinate permutation, a nonzero scalar rescaling, and
translation, then uses absolute continuity of finite-dimensional Gaussian
measure with respect to volume.
-/

open Matrix MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

private abbrev ComplexGramTwoSampleIndex := ((Fin 2 × Fin 2) × Fin 2)

/-- The source sample coordinates, in real/imaginary pairs, reindexed by the
row-major `Fin 8` coordinates used in the discriminant polynomial. -/
private def complexGramTwoSampleIndexEquiv :
    ComplexGramTwoSampleIndex ≃ Fin 8 :=
  Equiv.ofBijective
    (fun p : ComplexGramTwoSampleIndex =>
      complexGramTwoCoord p.1.1 p.1.2 (decide (p.2 = 1)))
    (by
      constructor
      · intro a b hab
        rcases a with ⟨⟨i, j⟩, r⟩
        rcases b with ⟨⟨i', j'⟩, r'⟩
        fin_cases i <;> fin_cases j <;> fin_cases r <;>
          fin_cases i' <;> fin_cases j' <;> fin_cases r' <;>
          simp_all [complexGramTwoCoord]
      · intro k
        fin_cases k
        · exact ⟨⟨(0, 0), 0⟩, by norm_num [complexGramTwoCoord]⟩
        · exact ⟨⟨(0, 0), 1⟩, by norm_num [complexGramTwoCoord]⟩
        · exact ⟨⟨(0, 1), 0⟩, by norm_num [complexGramTwoCoord]⟩
        · exact ⟨⟨(0, 1), 1⟩, by norm_num [complexGramTwoCoord]⟩
        · exact ⟨⟨(1, 0), 0⟩, by norm_num [complexGramTwoCoord]⟩
        · exact ⟨⟨(1, 0), 1⟩, by norm_num [complexGramTwoCoord]⟩
        · exact ⟨⟨(1, 1), 0⟩, by norm_num [complexGramTwoCoord]⟩
        · exact ⟨⟨(1, 1), 1⟩, by norm_num [complexGramTwoCoord]⟩)

/-- A measurable coordinate equivalence from the real eight-dimensional
complex sample space to the `Fin 8` coordinates in the polynomial model. -/
private def complexGramTwoSampleCoordEquiv :
    ComplexSample (m := 2) (n := 2) ≃ᵐ EuclideanSpace ℝ (Fin 8) :=
  ((MeasurableEquiv.toLp 2 (ComplexGramTwoSampleIndex → ℝ)).symm).trans
    ((MeasurableEquiv.piCongrLeft
      (fun _ : Fin 8 => ℝ)
      complexGramTwoSampleIndexEquiv).trans
        (MeasurableEquiv.toLp 2 (Fin 8 → ℝ)))

private theorem complexGramTwoSampleCoordEquiv_measurePreserving :
    MeasurePreserving complexGramTwoSampleCoordEquiv volume volume := by
  have h₁ : MeasurePreserving
      ((MeasurableEquiv.toLp 2 (ComplexGramTwoSampleIndex → ℝ)).symm)
      volume volume := PiLp.volume_preserving_ofLp _
  have h₂ : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin 8 => ℝ)
        complexGramTwoSampleIndexEquiv)
      volume volume :=
    volume_measurePreserving_piCongrLeft _ _
  have h₃ : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 8 → ℝ))
      volume volume := PiLp.volume_preserving_toLp _
  exact h₃.comp (h₂.comp h₁)

private theorem complexGramTwoSampleCoordEquiv_apply
    (z : ComplexSample (m := 2) (n := 2)) (i j : Fin 2) (k : Fin 2) :
    complexGramTwoSampleCoordEquiv z (complexGramTwoCoord i j (decide (k = 1))) =
      z ((i, j), k) := by
  simp only [complexGramTwoSampleCoordEquiv, MeasurableEquiv.trans_apply]
  have hcoord : complexGramTwoSampleIndexEquiv ((i, j), k) =
      complexGramTwoCoord i j (decide (k = 1)) := by
    change complexGramTwoCoord i j (decide (k = 1)) = _
    rfl
  rw [← hcoord]
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin 8 => ℝ) complexGramTwoSampleIndexEquiv
    (fun p : ComplexGramTwoSampleIndex => z p) ((i, j), k)

/-- The raw complex matrix in the discriminant file is the actual central
sample matrix after scaling its eight real coordinates by `1/√2`. -/
private theorem complexGramTwoSample_scaled_coordEquiv
    (z : ComplexSample (m := 2) (n := 2)) :
    complexGramTwoSample
        ((Real.sqrt (2 : ℝ))⁻¹ • WithLp.ofLp (complexGramTwoSampleCoordEquiv z)) =
      complexSampleMatrix z := by
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hreal (i j : Fin 2) :
      (WithLp.ofLp (complexGramTwoSampleCoordEquiv z))
        (complexGramTwoCoord i j false) = z ((i, j), 0) := by
    change complexGramTwoSampleCoordEquiv z (complexGramTwoCoord i j false) = _
    exact complexGramTwoSampleCoordEquiv_apply z i j 0
  have himag (i j : Fin 2) :
      (WithLp.ofLp (complexGramTwoSampleCoordEquiv z))
        (complexGramTwoCoord i j true) = z ((i, j), 1) := by
    change complexGramTwoSampleCoordEquiv z (complexGramTwoCoord i j true) = _
    exact complexGramTwoSampleCoordEquiv_apply z i j 1
  ext i j
  apply Complex.ext <;>
    simp [complexGramTwoSample, complexSampleMatrix,
      hreal, himag,
      Complex.div_ofReal_re, Complex.div_ofReal_im] <;>
    field_simp [hsqrt]

private def complexGramTwoDiscrEvent :
    Set (EuclideanSpace ℝ (Fin 8)) :=
  {y | Matrix.discr (complexGramTwoGram (WithLp.ofLp y)) = 0}

private theorem complexGramTwoDiscrEvent_measurable :
    MeasurableSet complexGramTwoDiscrEvent := by
  have hset : complexGramTwoDiscrEvent =
      {y : EuclideanSpace ℝ (Fin 8) |
        MvPolynomial.eval (WithLp.ofLp y) complexGramTwoDiscPoly = 0} := by
    ext y
    exact complexGramTwo_matrixDiscr_eq_zero_iff (WithLp.ofLp y)
  rw [hset]
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 8) =>
      MvPolynomial.eval (WithLp.ofLp y) complexGramTwoDiscPoly) := by
    exact (MvPolynomial.continuous_eval complexGramTwoDiscPoly).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin 8 => ℝ))
  exact isClosed_singleton.preimage hcont |>.measurableSet

private theorem complexGramTwoDiscrEvent_volume_eq_zero :
    volume complexGramTwoDiscrEvent = 0 := by
  have hpi :
      volume {y : Fin 8 → ℝ |
        Matrix.discr (complexGramTwoGram y) = 0} = 0 :=
    complexGramTwo_matrixDiscr_zeroSet_volume_eq_zero
  let e : (Fin 8 → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 8) :=
    MeasurableEquiv.toLp 2 _
  have hpres : MeasurePreserving e volume volume :=
    PiLp.volume_preserving_toLp (Fin 8)
  have hpre : e ⁻¹' complexGramTwoDiscrEvent =
      {y : Fin 8 → ℝ | Matrix.discr (complexGramTwoGram y) = 0} := by
    ext y
    simp [e, complexGramTwoDiscrEvent, complexGramTwoGram]
  have hmeasure :
      volume {y : Fin 8 → ℝ | Matrix.discr (complexGramTwoGram y) = 0} =
        volume complexGramTwoDiscrEvent := by
    rw [← hpre, ← hpres.map_eq]
    exact (e.map_apply complexGramTwoDiscrEvent).symm
  rw [← hmeasure]
  exact hpi

private theorem complexGramTwoScaledDiscrEvent_volume_eq_zero :
    volume ((fun y : EuclideanSpace ℝ (Fin 8) =>
      (Real.sqrt (2 : ℝ))⁻¹ • y) ⁻¹' complexGramTwoDiscrEvent) = 0 := by
  have hsqrt : (Real.sqrt (2 : ℝ))⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  rw [MeasureTheory.Measure.addHaar_preimage_smul
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
    hsqrt complexGramTwoDiscrEvent, complexGramTwoDiscrEvent_volume_eq_zero]
  simp

/-- The central `2 × 2` sample's zero-discriminant parameter set is Lebesgue-null. -/
private theorem complexGramTwoCentralSampleDiscr_volume_eq_zero :
    volume {z : ComplexSample (m := 2) (n := 2) |
      Matrix.discr (complexGram (complexSampleMatrix z)) = 0} = 0 := by
  let e := complexGramTwoSampleCoordEquiv
  let S := (fun y : EuclideanSpace ℝ (Fin 8) =>
    (Real.sqrt (2 : ℝ))⁻¹ • y) ⁻¹' complexGramTwoDiscrEvent
  have hset : {z : ComplexSample (m := 2) (n := 2) |
      Matrix.discr (complexGram (complexSampleMatrix z)) = 0} = e ⁻¹' S := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, S, complexGramTwoDiscrEvent]
    rw [← complexGramTwoSample_scaled_coordEquiv z]
    rfl
  have hmeasure : volume (e ⁻¹' S) = volume S := by
    rw [← complexGramTwoSampleCoordEquiv_measurePreserving.map_eq]
    exact (e.map_apply S).symm
  rw [hset, hmeasure]
  exact complexGramTwoScaledDiscrEvent_volume_eq_zero

/-- For every deterministic `2 × 2` complex mean, the actual shifted Gaussian
sample has zero probability of a repeated Gram eigenvalue. -/
theorem complexSample_shiftedGram_discriminant_zero_probability
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    stdGaussian (ComplexSample (m := 2) (n := 2))
      {z | Matrix.discr (complexGram (complexSampleMatrix z + M)) = 0} = 0 := by
  let S : Set (ComplexSample (m := 2) (n := 2)) :=
    {z | Matrix.discr (complexGram (complexSampleMatrix z)) = 0}
  have hshift :
      {z : ComplexSample (m := 2) (n := 2) |
        Matrix.discr (complexGram (complexSampleMatrix z + M)) = 0} =
        (fun z => z + complexSampleMean M) ⁻¹' S := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, S]
    rw [← complexSampleMatrix_add_mean z M]
  have hvol : volume
      {z : ComplexSample (m := 2) (n := 2) |
        Matrix.discr (complexGram (complexSampleMatrix z + M)) = 0} = 0 := by
    rw [hshift, measure_preimage_add_right,
      complexGramTwoCentralSampleDiscr_volume_eq_zero]
  rw [stdGaussian_euclidean_eq_radialDensity]
  exact withDensity_absolutelyContinuous volume _ hvol

/-- Equivalently, the discriminant-zero set has zero probability under the
noncentral complex Wishart law in the specific `m=n=2` model. -/
theorem complexNoncentralWishart_twoByTwo_discriminant_zero_probability
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    complexNoncentralWishart (m := 2) (n := 2) M
      {G | Matrix.discr G = 0} = 0 := by
  have hmeas : MeasurableSet {G : Matrix (Fin 2) (Fin 2) ℂ |
      Matrix.discr G = 0} := by
    have hcont : Continuous (fun G : Matrix (Fin 2) (Fin 2) ℂ => Matrix.discr G) := by
      simpa only [Matrix.discr_fin_two] using
        (by fun_prop : Continuous
          (fun G : Matrix (Fin 2) (Fin 2) ℂ => G.trace ^ 2 - 4 * G.det))
    exact isClosed_singleton.preimage hcont |>.measurableSet
  rw [complexNoncentralWishart, Measure.map_apply
    (measurable_shiftedComplexSampleGram M) hmeas]
  exact complexSample_shiftedGram_discriminant_zero_probability M

end

end JinWishart
