import JinWishartFormalization.AnalyticPositivePowerLimit
import JinWishartFormalization.CentralMinimumRealPolynomial
import JinWishartFormalization.CentralMinimumAllShapesDiversity
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Existence of a positive sharp central minimum hard-edge coefficient

The analytic continuation is separate from the actual piecewise CDF. This proves
existence and analytic factorization, NOT the classical factorial prefactor.
Codex. [需人工审查] Actual CDF and analytic continuation interpretation.
-/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

def centralMinimumCDFContinuation (d n : ℕ) (x : ℝ) : ℝ :=
  1-Real.exp (-((n+1 : ℕ) : ℝ)*x)*((centralDeterminantPowerMoment 0 (n+1) d)⁻¹*
    (centralMinimumRealPolynomial d (n+1)).eval x)

theorem analytic_centralMinimumCDFContinuation (d n : ℕ) (x : ℝ) :
    AnalyticAt ℝ (centralMinimumCDFContinuation d n) x := by
  have hpoly : AnalyticAt ℝ (fun x => (centralMinimumRealPolynomial d (n+1)).eval x) x := by
    exact AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) (centralMinimumRealPolynomial d (n+1)) x (Set.mem_univ x)
  unfold centralMinimumCDFContinuation
  exact analyticAt_const.sub
    (((analyticAt_const.mul analyticAt_id).rexp).mul (analyticAt_const.mul hpoly))

theorem actualCentralMinimumCDF_eq_continuation (d n : ℕ) (x : ℝ) (hx : 0≤x) :
    actualCentralMinimumCDF d n x=centralMinimumCDFContinuation d n x := by
  have he := actualCentralRectangular_minimum_CDF d (n+1) (Nat.succ_pos n) x hx
  rw [centralRectangularMinimumPolynomial_eq_realPolynomial] at he
  exact he

theorem centralMinimumCDFContinuation_pos_right (d n : ℕ) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<centralMinimumCDFContinuation d n x := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx hx1
  have hx0 : 0<x := hx
  rw [← actualCentralMinimumCDF_eq_continuation d n x hx0.le]
  exact lt_of_lt_of_le (by positivity)
    (actualCentralMinimumCDF_all_local_power_bounds d n x hx0 hx1.le).1

theorem centralMinimumCDFContinuation_log_exponent (d n : ℕ) :
    Tendsto (fun x => Real.log (centralMinimumCDFContinuation d n x)/Real.log x)
      (𝓝[>] 0) (𝓝 ((d+1 : ℕ) : ℝ)) := by
  apply (actualCentralMinimumCDF_all_diversity d n).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [actualCentralMinimumCDF_eq_continuation d n x (le_of_lt hx)]

theorem centralMinimumCDFContinuation_positive_factor (d n : ℕ) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ 0<g 0 ∧
      ∀ᶠ x in 𝓝 (0 : ℝ), centralMinimumCDFContinuation d n x=x^(d+1)*g x :=
  analytic_positive_factor_of_log_exponent _ (d+1)
    (analytic_centralMinimumCDFContinuation d n 0) (centralMinimumCDFContinuation_pos_right d n)
    (centralMinimumCDFContinuation_log_exponent d n)

theorem actualCentralMinimumCDF_sharp_positive_limit (d n : ℕ) :
    ∃ a : ℝ, 0<a ∧ Tendsto (fun x => actualCentralMinimumCDF d n x/x^(d+1))
      (𝓝[>] 0) (𝓝 a) := by
  obtain ⟨a,ha,ht⟩ := analytic_positive_power_ratio_limit _ (d+1)
    (analytic_centralMinimumCDFContinuation d n 0) (centralMinimumCDFContinuation_pos_right d n)
    (centralMinimumCDFContinuation_log_exponent d n)
  refine ⟨a,ha,ht.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [actualCentralMinimumCDF_eq_continuation d n x (le_of_lt hx)]

end
end JinWishart
#print axioms JinWishart.analytic_centralMinimumCDFContinuation
#print axioms JinWishart.actualCentralMinimumCDF_eq_continuation
#print axioms JinWishart.centralMinimumCDFContinuation_pos_right
#print axioms JinWishart.centralMinimumCDFContinuation_log_exponent
#print axioms JinWishart.centralMinimumCDFContinuation_positive_factor
#print axioms JinWishart.actualCentralMinimumCDF_sharp_positive_limit
