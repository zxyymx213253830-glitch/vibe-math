import JinWishartFormalization.TwoRowRandomDirectionLaw
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Four-real-coordinate Bartlett to Gram chart

Domain: first energy strictly positive. The map retains the first energy,
scales the two off-diagonal real coordinates by its square root, and adds
projection energy to residual energy.
[需人工审查] Coordinate volume convention and use in actual Gram density.
-/

open MeasureTheory
open scoped Matrix ENNReal

namespace JinWishart
noncomputable section

abbrev GramChartSpace := Fin 4 → ℝ

def twoRowGramChart (p : GramChartSpace) : GramChartSpace :=
  ![p 0, Real.sqrt (p 0) * p 1, Real.sqrt (p 0) * p 2, p 1 ^ 2 + p 2 ^ 2 + p 3]

def twoRowGramChartInverse (q : GramChartSpace) : GramChartSpace :=
  ![q 0, q 1 / Real.sqrt (q 0), q 2 / Real.sqrt (q 0),
    q 3 - ((q 1 / Real.sqrt (q 0)) ^ 2 + (q 2 / Real.sqrt (q 0)) ^ 2)]

def twoRowBartlettRealCoordinates (p : ℝ × (ℂ × ℝ)) : GramChartSpace :=
  ![p.1, p.2.1.re, p.2.1.im, p.2.2]

def twoRowGramRealCoordinates (M : Matrix (Fin 2) (Fin 2) ℂ) : GramChartSpace :=
  ![(M 0 0).re, (M 0 1).re, (M 0 1).im, (M 1 1).re]

/-- The real chart is exactly the existing actual-model Bartlett Gram map. -/
theorem twoRowGramChart_eq_BartlettGram_real (p : ℝ × (ℂ × ℝ)) :
    twoRowGramChart (twoRowBartlettRealCoordinates p) =
      twoRowGramRealCoordinates (twoRowBartlettGram p) := by
  have hn : ‖p.2.1‖ ^ 2 = p.2.1.re ^ 2 + p.2.1.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  ext i
  fin_cases i <;>
    simp [twoRowGramChart, twoRowBartlettRealCoordinates, twoRowGramRealCoordinates,
      twoRowBartlettGram, hn, ← Complex.ofReal_pow]

theorem twoRowGramChart_left_inverse (p : GramChartSpace) (hp : 0 < p 0) :
    twoRowGramChartInverse (twoRowGramChart p) = p := by
  have hn : Real.sqrt (p 0) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  ext i
  fin_cases i <;> simp [twoRowGramChart, twoRowGramChartInverse, hn]

theorem twoRowGramChart_injOn :
    Set.InjOn twoRowGramChart {p : GramChartSpace | 0 < p 0} := by
  intro p hp q hq h
  have hi := congrArg twoRowGramChartInverse h
  rwa [twoRowGramChart_left_inverse p hp, twoRowGramChart_left_inverse q hq] at hi

def twoRowGramChartDerivative (p : GramChartSpace) : GramChartSpace →L[ℝ] GramChartSpace :=
  ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0,
      (p 1 / (2 * Real.sqrt (p 0))) • ContinuousLinearMap.proj 0 +
        Real.sqrt (p 0) • ContinuousLinearMap.proj 1,
      (p 2 / (2 * Real.sqrt (p 0))) • ContinuousLinearMap.proj 0 +
        Real.sqrt (p 0) • ContinuousLinearMap.proj 2,
      (2 * p 1) • ContinuousLinearMap.proj 1 +
        (2 * p 2) • ContinuousLinearMap.proj 2 + ContinuousLinearMap.proj 3]

theorem hasFDerivAt_twoRowGramChart (p : GramChartSpace) (hp : 0 < p 0) :
    HasFDerivAt twoRowGramChart (twoRowGramChartDerivative p) p := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) p
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) p
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) p
  have h3 := hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) p
  have hs := h0.sqrt (ne_of_gt hp)
  unfold twoRowGramChart twoRowGramChartDerivative
  apply hasFDerivAt_pi.2
  intro i
  fin_cases i
  · simpa using h0
  · convert hs.mul h1 using 1 <;> ext v <;> simp <;> ring
  · convert hs.mul h2 using 1 <;> ext v <;> simp <;> ring
  · convert ((h1.pow 2).add (h2.pow 2)).add h3 using 1 <;> ext v <;> simp

theorem twoRowGramChartDerivative_det (p : GramChartSpace) (hp : 0 < p 0) :
    (twoRowGramChartDerivative p).toLinearMap.det = p 0 := by
  rw [← LinearMap.det_toMatrix']
  have ht : (LinearMap.toMatrix' (twoRowGramChartDerivative p).toLinearMap).IsLowerTriangular := by
    change ∀ ⦃i j : Fin 4⦄, i < j →
      LinearMap.toMatrix' (twoRowGramChartDerivative p).toLinearMap i j = 0
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [LinearMap.toMatrix'_apply, twoRowGramChartDerivative]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp [LinearMap.toMatrix'_apply, twoRowGramChartDerivative, Fin.prod_univ_succ,
    ← pow_two, Real.sq_sqrt (le_of_lt hp)]

/-- Nonnegative change of variables on the positive-first-energy chart.
This statement uses coordinate Lebesgue measure, not a claimed probability density. -/
theorem twoRowGramChart_lintegral_change (g : GramChartSpace → ℝ≥0∞) :
    ∫⁻ q in twoRowGramChart '' {p : GramChartSpace | 0 < p 0}, g q =
      ∫⁻ p in {p : GramChartSpace | 0 < p 0},
        ENNReal.ofReal (p 0) * g (twoRowGramChart p) := by
  have hs : MeasurableSet {p : GramChartSpace | 0 < p 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  calc
    _ = ∫⁻ p in {p : GramChartSpace | 0 < p 0},
        ENNReal.ofReal |(twoRowGramChartDerivative p).toLinearMap.det| *
          g (twoRowGramChart p) :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
        (fun p hp => (hasFDerivAt_twoRowGramChart p hp).hasFDerivWithinAt)
        twoRowGramChart_injOn g
    _ = _ := by
      apply setLIntegral_congr_fun hs
      intro p hp
      change ENNReal.ofReal |(twoRowGramChartDerivative p).toLinearMap.det| *
        g (twoRowGramChart p) = ENNReal.ofReal (p 0) * g (twoRowGramChart p)
      rw [twoRowGramChartDerivative_det p hp, abs_of_pos hp]

end
end JinWishart
