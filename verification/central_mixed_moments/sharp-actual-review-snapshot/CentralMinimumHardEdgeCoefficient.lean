import JinWishartFormalization.CentralMinimumSharpOrder
import JinWishartFormalization.AnalyticPowerTaylorCoefficient

/-!
# A derivative representation of the actual central sharp hard-edge coefficient

This is an explicit derivative of the finite factorial-functional exponential
polynomial, not an unevaluated probability integral. The simpler classical
factorial expression is still open. Codex.
[需人工审查] Actual probability/continuation and sharp-limit correspondence.
-/
open Filter
open scoped Topology
namespace JinWishart
noncomputable section

def centralMinimumHardEdgeCoefficient (d n : ℕ) : ℝ :=
  iteratedDeriv (d+1) (centralMinimumCDFContinuation d n) 0/((d+1).factorial : ℝ)

theorem centralMinimumCDFContinuation_derivatives_vanish (d n : ℕ) :
    ∀ j<d+1, iteratedDeriv j (centralMinimumCDFContinuation d n) 0=0 := by
  exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analytic_centralMinimumCDFContinuation d n 0)).mp
    (analytic_order_of_positive_log_exponent _ (d+1)
      (analytic_centralMinimumCDFContinuation d n 0) (centralMinimumCDFContinuation_pos_right d n)
      (centralMinimumCDFContinuation_log_exponent d n))).1

theorem centralMinimumHardEdgeCoefficient_pos (d n : ℕ) :
    0 < centralMinimumHardEdgeCoefficient d n :=
  analytic_power_taylor_coefficient_pos _ (d+1)
    (analytic_centralMinimumCDFContinuation d n 0) (centralMinimumCDFContinuation_pos_right d n)
    (centralMinimumCDFContinuation_log_exponent d n)

theorem actualCentralMinimumCDF_sharp_coefficient_limit (d n : ℕ) :
    Tendsto (fun x => actualCentralMinimumCDF d n x/x^(d+1)) (𝓝[>] 0)
      (𝓝 (centralMinimumHardEdgeCoefficient d n)) := by
  apply (analytic_power_ratio_taylor_limit _ (d+1)
    (analytic_centralMinimumCDFContinuation d n 0) (centralMinimumCDFContinuation_pos_right d n)
    (centralMinimumCDFContinuation_log_exponent d n)).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [actualCentralMinimumCDF_eq_continuation d n x (le_of_lt hx)]

end
end JinWishart
#print axioms JinWishart.centralMinimumCDFContinuation_derivatives_vanish
#print axioms JinWishart.centralMinimumHardEdgeCoefficient_pos
#print axioms JinWishart.actualCentralMinimumCDF_sharp_coefficient_limit
