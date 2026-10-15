import JinWishartFormalization.TwoRowScaledMinimum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Actual weakest-mode logarithmic-rate outage

Codex composes the established actual scaled Gram minimum law with an explicit
monotone event transformation. Natural logarithms give nats per mode. This does
not formalize the scalar Gaussian coding theorem, total MIMO mutual information,
power allocation, or a general noncentral Wishart law.
[需人工审查] Interpretation of rho as a per-mode signal-to-noise coefficient,
unit complex variance, and the operational interpretation of log(1+rho*gain).
Numerical preflight: experiments/two_row_log_rate_outage.py, seed 20261015,
200000 actual complex Gaussian samples and Gamma/Exp/eigensolver controls.
-/

open MeasureTheory ProbabilityTheory

namespace JinWishart
noncomputable section

/-- Generic event transformation, with positivity stated independently of any law. -/
theorem log_one_add_mul_le_iff (rho gain target : ℝ)
    (hrho : 0 < rho) (hgain : 0 ≤ gain) :
    Real.log (1 + rho * gain) ≤ target ↔
      gain ≤ (Real.exp target - 1) / rho := by
  rw [Real.log_le_iff_le_exp (by positivity), le_div_iff₀ hrho]
  constructor <;> intro h <;> nlinarith only [h]

/-- A mathematical log-rate statistic, using natural logarithms. -/
def twoRowWeakestLogRate (a rho : ℝ)
    (z : ComplexSample (m := 2) (n := 2)) : ℝ :=
  Real.log (1 + rho * twoRowActualMinimum (a • z))

theorem twoRowWeakestLogRate_nonneg (a rho : ℝ) (hrho : 0 ≤ rho)
    (z : ComplexSample (m := 2) (n := 2)) :
    0 ≤ twoRowWeakestLogRate a rho z := by
  apply Real.log_nonneg
  have h := mul_nonneg hrho (twoRowActualMinimum_nonneg (a • z))
  linarith only [h]

/-- Actual Gaussian probability, not a hypothesis about the target CDF.
[需人工审查] This event is for the weakest mode, not the sum of mode rates. -/
theorem actualTwoRow_weakestLogRate_outage (a rho target : ℝ)
    (ha : 0 < a) (hrho : 0 < rho) (htarget : 0 ≤ target) :
    ((stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | twoRowWeakestLogRate a rho z ≤ target}).toReal =
      1 - Real.exp (-2 * (((Real.exp target - 1) / rho) / a ^ 2)) := by
  have he : {z : ComplexSample (m := 2) (n := 2) |
      twoRowWeakestLogRate a rho z ≤ target} =
      {z | twoRowActualMinimum (a • z) ≤ (Real.exp target - 1) / rho} := by
    ext z
    exact log_one_add_mul_le_iff rho _ target hrho
      (twoRowActualMinimum_nonneg (a • z))
  rw [he]
  apply actualTwoRow_scaled_minimum_CDF a ha
  apply div_nonneg _ hrho.le
  have h : (1 : ℝ) ≤ Real.exp target := by
    simpa using Real.exp_le_exp.mpr htarget
  exact sub_nonneg.mpr h

/-- Negative targets have probability zero, by pointwise nonnegativity. -/
theorem actualTwoRow_weakestLogRate_outage_negative (a rho target : ℝ)
    (hrho : 0 ≤ rho) (htarget : target < 0) :
    (stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | twoRowWeakestLogRate a rho z ≤ target} = 0 := by
  have he : {z : ComplexSample (m := 2) (n := 2) |
      twoRowWeakestLogRate a rho z ≤ target} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have h := twoRowWeakestLogRate_nonneg a rho hrho z
    exact (not_le_of_gt htarget) (h.trans hz)
  rw [he, measure_empty]

end
end JinWishart

#print axioms JinWishart.log_one_add_mul_le_iff
#print axioms JinWishart.twoRowWeakestLogRate_nonneg
#print axioms JinWishart.actualTwoRow_weakestLogRate_outage
#print axioms JinWishart.actualTwoRow_weakestLogRate_outage_negative
