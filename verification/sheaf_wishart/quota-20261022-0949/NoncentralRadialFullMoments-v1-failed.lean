import JinWishartFormalization.PoissonFactorialMoments
import JinWishartFormalization.NaturalNuttallNormalization

/-! Codex. Seed2026102603 controls precede source. Every natural energy moment
of the normalized noncentral even-dimensional radial kernel, and the associated
full Nuttall integral. No Wishart joint spectral density is assumed.
[需人工审查] Absolute-summability/Fubini, integrability and model conventions. -/
open MeasureTheory Set Finset
namespace JinWishart
noncomputable section

private def radialMomentWeight (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(a^2/2))*((a^2/2)^n/(n.factorial : ℝ))

private def radialMomentTerm (q k : ℕ) (a : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (r^2/2)^k * chiEvenPoissonTerm q a r n

private theorem radialMomentTerm_factor (q k n : ℕ) (a r : ℝ) :
    radialMomentTerm q k a n r =
      (radialMomentWeight a n/(2^(n+q+k)*((n+q).factorial : ℝ)))*
        (r^(2*(n+q+k)+1)*Real.exp (-(r^2/2))) := by
  have hp : (r^2/2)^k*r^(2*n+2*q+1) = r^(2*(n+q+k)+1)/2^k := by
    rw [div_pow, ← pow_mul, div_mul_eq_mul_div, ← pow_add]
    congr 2
    omega
  have hd : (2 : ℝ)^k*2^(n+q) = 2^(n+q+k) := by
    rw [← pow_add]
    congr 1
    omega
  unfold radialMomentTerm chiEvenPoissonTerm radialMomentWeight
  calc
    _ = (Real.exp (-(a^2/2))*((a^2/2)^n/(n.factorial : ℝ)))*
        (((r^2/2)^k*r^(2*n+2*q+1))*Real.exp (-(r^2/2)) /
          (2^(n+q)*((n+q).factorial : ℝ))) := by ring
    _ = _ := by
      rw [hp, ← hd]
      field_simp
      <;> ring

private theorem radialMomentTerm_integral (q k n : ℕ) (a : ℝ) :
    (∫ r in Ioi (0 : ℝ), radialMomentTerm q k a n r) =
      radialMomentWeight a n *
        (((n+q+k).factorial : ℝ)/((n+q).factorial : ℝ)) := by
  rw [funext (radialMomentTerm_factor q k n a), integral_const_mul, gaussianOddMoment_general]
  have hnq : ((n+q).factorial : ℝ) ≠ 0 := by positivity
  have hp : (2 : ℝ)^(n+q+k) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem radialMomentTerm_integrable (q k n : ℕ) (a : ℝ) :
    IntegrableOn (radialMomentTerm q k a n) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun r : ℝ => r^(2*(n+q+k)+1)*Real.exp (-(r^2/2))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ))
      (s := ((2*(n+q+k)+1 : ℕ) : ℝ)) (by norm_num)
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ)<0) (Nat.cast_nonneg _))
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 h
    intro r _
    rw [Real.rpow_natCast]
    congr 1
    ring
  rw [funext (radialMomentTerm_factor q k n a)]
  exact hbase.const_mul _

private theorem radialMomentPolynomial_pos (q k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 < poissonFactorialMomentPolynomial q k x := by
  unfold poissonFactorialMomentPolynomial
  apply mul_pos (by positivity)
  have hc : 0 < ((q+k).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (show k ≤ q+k by omega)
  have hs := single_le_sum
    (f := fun j : ℕ => ((q+k).choose (k-j) : ℝ)*x^j/(j.factorial : ℝ))
    (s := range (k+1)) (fun j _ => by positivity)
    (show 0 ∈ range (k+1) by simp)
  simpa only [Nat.sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] using
    lt_of_lt_of_le hc hs

theorem noncentralChiEvenRadialKernel_energyMoment (q k : ℕ) (a : ℝ) :
    (∫ r in Ioi (0 : ℝ), (r^2/2)^k*noncentralChiEvenRadialKernel q a r) =
      poissonFactorialMomentPolynomial q k (a^2/2) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hF : ∀ n : ℕ, Integrable (radialMomentTerm q k a n) μ :=
    fun n => radialMomentTerm_integrable q k n a
  have hnorm (n : ℕ) : (∫ r, ‖radialMomentTerm q k a n r‖ ∂μ) =
      radialMomentWeight a n*(((n+q+k).factorial : ℝ)/((n+q).factorial : ℝ)) := by
    calc
      _ = ∫ r, radialMomentTerm q k a n r ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        rw [Real.norm_eq_abs, abs_of_nonneg (by
          unfold radialMomentTerm chiEvenPoissonTerm
          have hr0 : 0 < r := hr
          positivity)]
      _ = _ := radialMomentTerm_integral q k n a
  have hsum : Summable (fun n : ℕ => ∫ r, ‖radialMomentTerm q k a n r‖ ∂μ) := by
    apply ((poisson_factorialMoment_hasSum q k (a^2/2)).summable.mul_left
      (Real.exp (-(a^2/2)))).congr
    intro n
    rw [hnorm]
    unfold radialMomentWeight
    ring
  have he (r : ℝ) : (r^2/2)^k*noncentralChiEvenRadialKernel q a r =
      ∑' n : ℕ, radialMomentTerm q k a n r := by
    rw [noncentralChiEvenRadialKernel_eq_poissonMixture]
    unfold radialMomentTerm
    rw [tsum_mul_left]
  change (∫ r, (r^2/2)^k*noncentralChiEvenRadialKernel q a r ∂μ) = _
  rw [funext he, ← integral_tsum_of_summable_integral_norm hF hsum]
  simp_rw [show ∀ n : ℕ, (∫ r, radialMomentTerm q k a n r ∂μ) =
    radialMomentWeight a n*(((n+q+k).factorial : ℝ)/((n+q).factorial : ℝ)) from
      fun n => radialMomentTerm_integral q k n a]
  simp only [radialMomentWeight, mul_assoc]
  rw [tsum_mul_left, (poisson_factorialMoment_hasSum q k (a^2/2)).tsum_eq,
    ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

theorem integrableOn_noncentralChiEvenRadialKernel_energyMoment (q k : ℕ) (a : ℝ) :
    IntegrableOn (fun r : ℝ => (r^2/2)^k*noncentralChiEvenRadialKernel q a r) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [noncentralChiEvenRadialKernel_energyMoment]
  exact ne_of_gt (radialMomentPolynomial_pos q k (a^2/2) (by positivity))

private theorem fullNuttallIntegrand_factor (q k : ℕ) (a r : ℝ) :
    nuttallQIntegrand (q+2*k+1) q a r =
      ((a : ℂ)^q*(2 : ℂ)^k)*(((r^2/2)^k*noncentralChiEvenRadialKernel q a r : ℝ) : ℂ) := by
  have hp : nuttallQIntegrand (q+2*k+1) q a r =
      (r : ℂ)^(2*k)*nuttallQIntegrand (q+1) q a r := by
    unfold nuttallQIntegrand
    rw [show q+2*k+1=2*k+(q+1) by omega, pow_add]
    ring
  rw [hp, nuttallQIntegrand_eq_evenRadialKernel]
  push_cast
  rw [div_pow, ← pow_mul]
  have ht : (2 : ℂ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  <;> ring

theorem nuttallQ_fullNaturalMoment (q k : ℕ) (a : ℝ) :
    nuttallQ (q+2*k+1) q a 0 = (a : ℂ)^q*(2 : ℂ)^k*
      (poissonFactorialMomentPolynomial q k (a^2/2) : ℂ) := by
  unfold nuttallQ
  rw [funext (fullNuttallIntegrand_factor q k a), integral_const_mul,
    integral_complex_ofReal, noncentralChiEvenRadialKernel_energyMoment]

theorem integrableOn_nuttallQ_fullNaturalMoment (q k : ℕ) (a : ℝ) :
    IntegrableOn (nuttallQIntegrand (q+2*k+1) q a) (Ioi 0) := by
  rw [funext (fullNuttallIntegrand_factor q k a)]
  exact (integrableOn_noncentralChiEvenRadialKernel_energyMoment q k a).ofReal.const_mul _

end
end JinWishart
#print axioms JinWishart.noncentralChiEvenRadialKernel_energyMoment
#print axioms JinWishart.integrableOn_noncentralChiEvenRadialKernel_energyMoment
#print axioms JinWishart.nuttallQ_fullNaturalMoment
#print axioms JinWishart.integrableOn_nuttallQ_fullNaturalMoment
