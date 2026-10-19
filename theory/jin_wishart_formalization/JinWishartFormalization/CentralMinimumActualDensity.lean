import JinWishartFormalization.CentralMinimumSharpOrder
import JinWishartFormalization.MeasureFromPositivePrimitive
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Actual general CENTRAL least-eigenvalue density from its proved CDF

This is a one-dimensional marginal density, NOT the joint spectral density G2.
No target PDF is assumed. Variance-one complex entries, raw Gram, N=n+1>0.
Codex. [需人工审查] CDF/FTC/withDensity boundary and actual-model interpretation.
-/
open Set Filter MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def centralMinimumPDFCore (d n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((n+1 : ℕ) : ℝ)*x)*(centralDeterminantPowerMoment 0 (n+1) d)⁻¹*
    (((n+1 : ℕ) : ℝ)*(centralMinimumRealPolynomial d (n+1)).eval x-
      (centralMinimumRealPolynomial d (n+1)).derivative.eval x)

theorem continuous_centralMinimumPDFCore (d n : ℕ) : Continuous (centralMinimumPDFCore d n) := by
  unfold centralMinimumPDFCore
  fun_prop

theorem hasDerivAt_centralMinimumCDFContinuation (d n : ℕ) (x : ℝ) :
    HasDerivAt (centralMinimumCDFContinuation d n) (centralMinimumPDFCore d n x) x := by
  have hE := ((hasDerivAt_id x).const_mul (-((n+1 : ℕ) : ℝ))).exp
  have hP := ((centralMinimumRealPolynomial d (n+1)).hasDerivAt x).const_mul
    ((centralDeterminantPowerMoment 0 (n+1) d)⁻¹)
  convert (hasDerivAt_const x (1 : ℝ)).sub (hE.mul hP) using 1 <;>
    (try funext y) <;>
    (try dsimp only [centralMinimumCDFContinuation,centralMinimumPDFCore,id_eq,Pi.sub_apply,Pi.mul_apply]) <;> ring

theorem centralMinimumCDFContinuation_zero (d n : ℕ) : centralMinimumCDFContinuation d n 0=0 := by
  have h := centralRectangularMinimumPolynomial_eq_realPolynomial d (n+1) 0
  rw [centralRectangularMinimumPolynomial_zero] at h
  unfold centralMinimumCDFContinuation
  simp only [mul_zero,Real.exp_zero,one_mul]
  rw [← h]
  ring

theorem actualCentralMinimum_cdf_eq_piecewise_continuation (d n : ℕ) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).map
      (centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n))) x =
        if 0≤x then centralMinimumCDFContinuation d n x else 0 := by
  simpa only [centralRectangularMinimumPolynomial_eq_realPolynomial,centralMinimumCDFContinuation] using
    actualCentralRectangular_minimum_cdf_function d (n+1) (Nat.succ_pos n) x

theorem centralMinimumPDFCore_nonneg (d n : ℕ) (x : ℝ) (hx : 0<x) :
    0≤centralMinimumPDFCore d n x := by
  apply primitive_derivative_nonneg_of_cdf
    ((stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).map
      (centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n)))
    (centralMinimumCDFContinuation d n) (centralMinimumPDFCore d n)
    (actualCentralMinimum_cdf_eq_piecewise_continuation d n)
    (hasDerivAt_centralMinimumCDFContinuation d n) x hx

theorem actualCentralMinimum_map_eq_density (d n : ℕ) :
    ((stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).map
      (centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n))) =
      volume.withDensity ((Ioi (0 : ℝ)).indicator
        (fun x => ENNReal.ofReal (centralMinimumPDFCore d n x))) := by
  exact measure_eq_withDensity_of_positive_primitive _ _ _
    (centralMinimumCDFContinuation_zero d n) (actualCentralMinimum_cdf_eq_piecewise_continuation d n)
    (continuous_centralMinimumPDFCore d n) (hasDerivAt_centralMinimumCDFContinuation d n)
    (centralMinimumPDFCore_nonneg d n)

end
end JinWishart
#print axioms JinWishart.continuous_centralMinimumPDFCore
#print axioms JinWishart.hasDerivAt_centralMinimumCDFContinuation
#print axioms JinWishart.centralMinimumCDFContinuation_zero
#print axioms JinWishart.actualCentralMinimum_cdf_eq_piecewise_continuation
#print axioms JinWishart.centralMinimumPDFCore_nonneg
#print axioms JinWishart.actualCentralMinimum_map_eq_density
