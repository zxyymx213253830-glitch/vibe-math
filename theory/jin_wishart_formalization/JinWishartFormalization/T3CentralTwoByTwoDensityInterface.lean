import JinWishartFormalization.OrderedEigenvalueMeasurable

/-!
# Central `2 × 2` Theorem 3: density-to-event interface

For `s=t=2`, rank `L=0`, and `k=2`, the increment event in Theorem 3 is
`φ₂ < x < φ₁`. The paper's central ordered eigenvalue density specializes to
`exp (-(φ₁+φ₂)) * (φ₁-φ₂)^2` on `0 < φ₂ < φ₁`.

This file formalizes the concrete event, its spectral pushforward law, the
candidate density, and the implication from the missing pushforward-density
identity to the desired integral representation. It does NOT assert that
identity: proving it requires the complex Wishart eigenvalue change of
variables/Jacobian and angular normalization, which are not present in the
current development. [需人工审查]
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace JinWishart

noncomputable section

/-- The two ordered eigenvalues of the central complex `2 × 2` Gram sample,
as a measurable map into the eigenvalue plane. -/
def centralTwoByTwoEigenpair
    (z : ComplexSample (m := 2) (n := 2)) : ℝ × ℝ :=
  (complexNoncentralSampleEigenvalue
      (0 : Matrix (Fin 2) (Fin 2) ℂ) (⟨0, by simp⟩ : Fin (Fintype.card (Fin 2))) z,
    complexNoncentralSampleSmallestEigenvalue
      (0 : Matrix (Fin 2) (Fin 2) ℂ) (by norm_num) z)

theorem measurable_centralTwoByTwoEigenpair :
    Measurable (centralTwoByTwoEigenpair) := by
  exact Measurable.prodMk
    (measurable_complexNoncentralSampleLargestEigenvalue
      (m := 2) (n := 2) (0 : Matrix (Fin 2) (Fin 2) ℂ) (by norm_num))
    (measurable_complexNoncentralSampleSmallestEigenvalue
      (m := 2) (n := 2) (0 : Matrix (Fin 2) (Fin 2) ℂ) (by norm_num))

/-- The open threshold-crossing region for `k=2` in the ordered `2 × 2`
case: the smaller eigenvalue is below `x`, and the larger one above it. -/
def centralTwoByTwoT3Region (x : ℝ) : Set (ℝ × ℝ) :=
  {y | y.2 < x ∧ x < y.1}

theorem measurableSet_centralTwoByTwoT3Region (x : ℝ) :
    MeasurableSet (centralTwoByTwoT3Region x) := by
  exact (measurableSet_lt measurable_snd measurable_const).inter
    (measurableSet_lt measurable_const measurable_fst)

/-- The actual central `2 × 2` increment probability, defined on the original
standard complex-Gaussian sample space rather than by an abstract recurrence. -/
def centralTwoByTwoT3Increment (x : ℝ) : ℝ≥0∞ :=
  stdGaussian (ComplexSample (m := 2) (n := 2))
    (centralTwoByTwoEigenpair ⁻¹' centralTwoByTwoT3Region x)

/-- The joint law of the two ordered eigenvalues of the central Gram sample. -/
def centralTwoByTwoJointEigenvalueLaw : Measure (ℝ × ℝ) :=
  (stdGaussian (ComplexSample (m := 2) (n := 2))).map
    centralTwoByTwoEigenpair

/-- The central ordered `2 × 2` Wishart density from the paper, extended by
zero outside the ordered positive chamber. In the chamber its normalization
constant is one: `Γ₂(2)=1` and the two Vandermonde factors combine to the
square shown here. -/
def centralTwoByTwoPaperEigenvalueDensity (y : ℝ × ℝ) : ℝ≥0∞ :=
  if 0 < y.2 ∧ y.2 < y.1 then
    ENNReal.ofReal (Real.exp (-(y.1 + y.2)) * (y.1 - y.2) ^ 2)
  else 0

/-- Earliest missing probability bridge for this smallest nontrivial instance:
if the actual ordered-eigenvalue pushforward law has the central Wishart
density, then Theorem 3's concrete increment event is exactly its integral
over `φ₂ < x < φ₁`. The density identification is an explicit premise, not
an axiom or placeholder. -/
theorem centralTwoByTwoT3Increment_eq_densityIntegral
    (x : ℝ)
    (hDensity : centralTwoByTwoJointEigenvalueLaw =
      (volume : Measure (ℝ × ℝ)).withDensity
        centralTwoByTwoPaperEigenvalueDensity) :
    centralTwoByTwoT3Increment x =
        ∫⁻ y in centralTwoByTwoT3Region x,
        centralTwoByTwoPaperEigenvalueDensity y ∂(volume : Measure (ℝ × ℝ)) := by
  change stdGaussian (ComplexSample (m := 2) (n := 2))
      (centralTwoByTwoEigenpair ⁻¹' centralTwoByTwoT3Region x) = _
  calc
    _ = centralTwoByTwoJointEigenvalueLaw (centralTwoByTwoT3Region x) := by
      rw [centralTwoByTwoJointEigenvalueLaw]
      exact (Measure.map_apply measurable_centralTwoByTwoEigenpair
        (measurableSet_centralTwoByTwoT3Region x)).symm
    _ = _ := by
      rw [hDensity, withDensity_apply _ (measurableSet_centralTwoByTwoT3Region x)]

end

end JinWishart
