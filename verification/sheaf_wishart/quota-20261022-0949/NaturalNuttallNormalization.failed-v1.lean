import JinWishartFormalization.BesselINaturalSeries
import JinWishartFormalization.NuttallQBoundary
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! All-natural-order analytic Nuttall normalization from existing Poisson
kernel and odd Gaussian moments. Codex, controls seed2026102249 before source.
[需人工审查] Countable sums/integrals, norm integrability and totalization.
This does not identify a general shifted Gaussian sample law. -/
open MeasureTheory Set
namespace JinWishart
noncomputable section

private def evenPoissonWeight (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(a^2/2))*((a^2/2)^n/(n.factorial : ℝ))

private theorem evenTermFactor (q : ℕ) (a : ℝ) (n : ℕ) (r : ℝ) :
    chiEvenPoissonTerm q a r n=
      (evenPoissonWeight a n/(2^(n+q)*((n+q).factorial : ℝ)))*
        (r^(2*(n+q)+1)*Real.exp (-(r^2/2))) := by
  unfold chiEvenPoissonTerm evenPoissonWeight
  rw [show 2*n+2*q+1=2*(n+q)+1 by omega]
  ring

private theorem evenTermIntegral (q : ℕ) (a : ℝ) (n : ℕ) :
    (∫ r in Ioi (0 : ℝ),chiEvenPoissonTerm q a r n)=evenPoissonWeight a n := by
  have hf : (fun r : ℝ => chiEvenPoissonTerm q a r n)=
      fun r => (evenPoissonWeight a n/(2^(n+q)*((n+q).factorial : ℝ)))*
        (r^(2*(n+q)+1)*Real.exp (-(r^2/2))) := funext (evenTermFactor q a n)
  rw [hf,integral_const_mul,gaussianOddMoment_general]
  exact div_mul_cancel₀ _ (by positivity)

private theorem evenTermIntegrable (q : ℕ) (a : ℝ) (n : ℕ) :
    IntegrableOn (fun r : ℝ => chiEvenPoissonTerm q a r n) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun r : ℝ => r^(2*(n+q)+1)*Real.exp (-(r^2/2))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ))
      (s := ((2*(n+q)+1 : ℕ) : ℝ)) (by norm_num) (by positivity)
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 h
    intro r _
    rw [Real.rpow_natCast]
    congr 1
    ring
  have hf : (fun r : ℝ => chiEvenPoissonTerm q a r n)=
      fun r => (evenPoissonWeight a n/(2^(n+q)*((n+q).factorial : ℝ)))*
        (r^(2*(n+q)+1)*Real.exp (-(r^2/2))) := funext (evenTermFactor q a n)
  rw [hf]
  exact hbase.const_mul _

theorem noncentralChiEvenRadialKernel_integral_eq_one (q : ℕ) (a : ℝ) :
    (∫ r in Ioi (0 : ℝ),noncentralChiEvenRadialKernel q a r)=1 := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hFint : ∀ n : ℕ,Integrable (fun r : ℝ => chiEvenPoissonTerm q a r n) μ :=
    fun n => evenTermIntegrable q a n
  have hnorm (n : ℕ) : (∫ r,‖chiEvenPoissonTerm q a r n‖ ∂μ)=evenPoissonWeight a n := by
    calc
      _=(∫ r,chiEvenPoissonTerm q a r n ∂μ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        rw [Real.norm_eq_abs,abs_of_nonneg (by
          unfold chiEvenPoissonTerm
          have hr0 : 0<r := hr
          positivity)]
      _=_ := evenTermIntegral q a n
  have hsum_norm : Summable (fun n : ℕ => ∫ r,‖chiEvenPoissonTerm q a r n‖ ∂μ) := by
    have hs := (Real.summable_pow_div_factorial (a^2/2)).mul_left (Real.exp (-(a^2/2)))
    exact hs.congr (fun n => (hnorm n).symm)
  have hsum : (∑' n : ℕ,evenPoissonWeight a n)=1 := by
    unfold evenPoissonWeight
    rw [tsum_mul_left]
    have hexp (x : ℝ) : (∑' n : ℕ,x^n/(n.factorial : ℝ))=Real.exp x := by
      rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum ℝ]
      apply tsum_congr
      intro n
      simp [div_eq_mul_inv,smul_eq_mul,mul_comm]
    rw [hexp,← Real.exp_add,neg_add_cancel,Real.exp_zero]
  change (∫ r,noncentralChiEvenRadialKernel q a r ∂μ)=1
  calc
    _=(∫ r,(∑' n : ℕ,chiEvenPoissonTerm q a r n) ∂μ) := by
      apply integral_congr_ae
      exact ae_of_all _ (noncentralChiEvenRadialKernel_eq_poissonMixture q a)
    _=∑' n : ℕ,(∫ r,chiEvenPoissonTerm q a r n ∂μ) :=
      (integral_tsum_of_summable_integral_norm hFint hsum_norm).symm
    _=∑' n : ℕ,evenPoissonWeight a n := by
      apply tsum_congr
      intro n
      exact evenTermIntegral q a n
    _=1 := hsum

theorem integrableOn_noncentralChiEvenRadialKernel (q : ℕ) (a : ℝ) :
    IntegrableOn (noncentralChiEvenRadialKernel q a) (Ioi 0) := by
  exact Integrable.of_integral_ne_zero (by rw [noncentralChiEvenRadialKernel_integral_eq_one];norm_num)

theorem nuttallQ_succ_self_zero (q : ℕ) (a : ℝ) :
    nuttallQ (q+1) q a 0=(a : ℂ)^q := by
  unfold nuttallQ
  have hf : nuttallQIntegrand (q+1) q a=
      fun r : ℝ => (a : ℂ)^q*(noncentralChiEvenRadialKernel q a r : ℂ) :=
    funext (nuttallQIntegrand_eq_evenRadialKernel q a)
  rw [hf,integral_const_mul,integral_complex_ofReal,
    noncentralChiEvenRadialKernel_integral_eq_one,Complex.ofReal_one,mul_one]

end
end JinWishart
#print axioms JinWishart.noncentralChiEvenRadialKernel_integral_eq_one
#print axioms JinWishart.integrableOn_noncentralChiEvenRadialKernel
#print axioms JinWishart.nuttallQ_succ_self_zero
