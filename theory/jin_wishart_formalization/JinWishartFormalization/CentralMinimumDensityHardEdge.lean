import JinWishartFormalization.CentralMinimumActualDensity
import JinWishartFormalization.CentralMinimumFiniteHardEdgeCoefficient
import JinWishartFormalization.AnalyticVanishingPowerLimit

/-! Sharp right-edge asymptotic of the actual central ONE-dimensional PDF.
Codex. [需人工审查] Actual density/edge convention, inherited measure interpretation. -/
open Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem centralMinimumPDFCore_sharp_coefficient_limit (d n : ℕ) :
    Tendsto (fun x => centralMinimumPDFCore d n x/x^d) (𝓝[>] 0)
      (𝓝 (((d+1 : ℕ) : ℝ)*centralMinimumFiniteHardEdgeCoefficient d n)) := by
  have he : deriv (centralMinimumCDFContinuation d n)=centralMinimumPDFCore d n :=
    funext (fun x => (hasDerivAt_centralMinimumCDFContinuation d n x).deriv)
  have ha : AnalyticAt ℝ (centralMinimumPDFCore d n) 0 := by
    rw [← he]
    exact (analytic_centralMinimumCDFContinuation d n 0).deriv
  have hz : ∀ i<d, iteratedDeriv i (centralMinimumPDFCore d n) 0=0 := by
    intro i hi
    rw [← he,← iteratedDeriv_succ']
    exact centralMinimumCDFContinuation_derivatives_vanish d n (i+1) (by omega)
  have ht := analytic_ratio_limit_of_vanishing _ d ha hz
  have hc : iteratedDeriv d (centralMinimumPDFCore d n) 0/(d.factorial : ℝ)=
      ((d+1 : ℕ) : ℝ)*centralMinimumFiniteHardEdgeCoefficient d n := by
    rw [← he,← iteratedDeriv_succ',← centralMinimumHardEdgeCoefficient_eq_finite]
    unfold centralMinimumHardEdgeCoefficient
    rw [Nat.factorial_succ,Nat.cast_mul]
    have hfac : (d.factorial : ℝ)≠0 := by positivity
    have hs : ((d+1 : ℕ) : ℝ)≠0 := by positivity
    field_simp
  rwa [hc] at ht

end
end JinWishart
#print axioms JinWishart.centralMinimumPDFCore_sharp_coefficient_limit
