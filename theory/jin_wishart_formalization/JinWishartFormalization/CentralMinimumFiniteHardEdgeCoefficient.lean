import JinWishartFormalization.CentralMinimumHardEdgeCoefficient
import JinWishartFormalization.ExponentialPolynomialTaylor

/-!
# Finite factorial-functional coefficient of the sharp actual hard-edge law

No derivative or probability integral remains in this coefficient. The real
polynomial coefficients are already defined by a finite Gaussian factorial
functional. This is NOT identification with the classical simplified constant.
Codex. [需人工审查] Inherited actual-model/Taylor interpretation.
-/
open Filter
open scoped Topology
namespace JinWishart
noncomputable section

def centralMinimumFiniteHardEdgeCoefficient (d n : ℕ) : ℝ :=
  -(centralDeterminantPowerMoment 0 (n+1) d)⁻¹ / ((d+1).factorial : ℝ) *
    ∑ i ∈ Finset.range (d+2), ((d+1).choose i : ℝ)*(-((n+1 : ℕ) : ℝ))^i*
      ((d+1-i).factorial : ℝ)*(centralMinimumRealPolynomial d (n+1)).coeff (d+1-i)

theorem centralMinimumHardEdgeCoefficient_eq_finite (d n : ℕ) :
    centralMinimumHardEdgeCoefficient d n = centralMinimumFiniteHardEdgeCoefficient d n := by
  have he : centralMinimumCDFContinuation d n = (fun x : ℝ => 1-
      (Real.exp (-((n+1 : ℕ) : ℝ)*x)*(centralMinimumRealPolynomial d (n+1)).eval x)*
        (centralDeterminantPowerMoment 0 (n+1) d)⁻¹) := by
    funext x
    unfold centralMinimumCDFContinuation
    ring
  unfold centralMinimumHardEdgeCoefficient
  rw [he,iteratedDeriv_const_sub (Nat.succ_pos d) (1 : ℝ),iteratedDeriv_neg,
    iteratedDeriv_mul_const_field,iteratedDeriv_exp_mul_polynomial_zero]
  unfold centralMinimumFiniteHardEdgeCoefficient
  ring

theorem centralMinimumFiniteHardEdgeCoefficient_pos (d n : ℕ) :
    0 < centralMinimumFiniteHardEdgeCoefficient d n := by
  rw [← centralMinimumHardEdgeCoefficient_eq_finite]
  exact centralMinimumHardEdgeCoefficient_pos d n

theorem actualCentralMinimumCDF_finite_sharp_coefficient_limit (d n : ℕ) :
    Tendsto (fun x => actualCentralMinimumCDF d n x/x^(d+1)) (𝓝[>] 0)
      (𝓝 (centralMinimumFiniteHardEdgeCoefficient d n)) := by
  rw [← centralMinimumHardEdgeCoefficient_eq_finite]
  exact actualCentralMinimumCDF_sharp_coefficient_limit d n

end
end JinWishart
#print axioms JinWishart.centralMinimumHardEdgeCoefficient_eq_finite
#print axioms JinWishart.centralMinimumFiniteHardEdgeCoefficient_pos
#print axioms JinWishart.actualCentralMinimumCDF_finite_sharp_coefficient_limit
