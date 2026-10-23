import JinWishartFormalization.BesselI1Series
import JinWishartFormalization.NoncentralEvenDimensionalPoissonMixture

/-! Natural-order modified Bessel factorial series from the actual definition.
Codex. Seed2026102249 controls precede source. Reuses the regularized0F1
definition and integer Gamma coefficients; no assumed angular identity. -/
namespace JinWishart
noncomputable section

private theorem modifiedBesselI_nat_regularized (q : ℕ) (z : ℂ) :
    modifiedBesselI q z=(z/2)^q*
      Complex.regularizedHGFun 0 {(q : ℂ)+1} (z^2/4) := by
  simp only [modifiedBesselI,Complex.besselJ_def,Int.cast_natCast,Complex.cpow_natCast]
  have hz : -((Complex.I*z/2)^2)=z^2/4 := by
    simp only [div_pow,mul_pow,Complex.I_sq]
    ring
  rw [hz]
  rw [← mul_assoc,← mul_pow]
  congr 2
  simp [Complex.I_sq]

private theorem naturalBesselCoefficient (q n : ℕ) :
    Complex.regularizedHGFunCoeff 0 {(q : ℂ)+1} n=
      (((n.factorial : ℂ)*((n+q).factorial : ℂ))⁻¹) := by
  simp only [Complex.regularizedHGFunCoeff,Multiset.map_zero,Multiset.prod_zero,
    Multiset.map_singleton,Multiset.prod_singleton]
  have harg : ((q : ℂ)+1)+(n : ℂ)=((n+q : ℕ) : ℂ)+1 := by push_cast;ring
  rw [harg,Complex.Gamma_nat_eq_factorial]
  field_simp

theorem modifiedBesselI_nat_eq_factorialSeries (q : ℕ) (z : ℂ) :
    modifiedBesselI q z=(z/2)^q*∑' n : ℕ,
      (z^2/4)^n/((n.factorial : ℂ)*((n+q).factorial : ℂ)) := by
  rw [modifiedBesselI_nat_regularized]
  have hs : Complex.regularizedHGFun 0 {(q : ℂ)+1} (z^2/4)=
      ∑' n : ℕ,Complex.regularizedHGFunCoeff 0 {(q : ℂ)+1} n*(z^2/4)^n := by
    rw [Complex.regularizedHGFun,Complex.regularizedHGFunSeries]
    change FormalMultilinearSeries.ofScalarsSum
      (Complex.regularizedHGFunCoeff 0 {(q : ℂ)+1}) (z^2/4)=_
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp only [smul_eq_mul]
  rw [hs]
  congr 1
  apply tsum_congr
  intro n
  rw [naturalBesselCoefficient]
  ring

theorem modifiedBesselI_nat_ofReal_eq_realSeries (q : ℕ) (x : ℝ) :
    (((x/2)^q*∑' n : ℕ,(x^2/4)^n/
      ((n.factorial : ℝ)*((n+q).factorial : ℝ)) : ℝ) : ℂ)=
      modifiedBesselI q (x : ℂ) := by
  rw [Complex.ofReal_mul,Complex.ofReal_tsum,modifiedBesselI_nat_eq_factorialSeries]
  push_cast
  congr 1
  apply tsum_congr
  intro n
  push_cast
  ring

theorem nuttallQIntegrand_eq_evenRadialKernel (q : ℕ) (a r : ℝ) :
    nuttallQIntegrand (q+1) q a r=(a : ℂ)^q*
      (noncentralChiEvenRadialKernel q a r : ℂ) := by
  rw [nuttallQIntegrand,← modifiedBesselI_nat_ofReal_eq_realSeries]
  unfold noncentralChiEvenRadialKernel
  push_cast
  rw [div_pow,mul_pow]
  have hp : (r : ℂ)^(q+1)*(r : ℂ)^q=(r : ℂ)^(2*q+1) := by rw [← pow_add];congr 1;omega
  have h2 : (2 : ℂ)^q≠0 := by positivity
  field_simp [h2]
  rw [← hp]
  ring

end
end JinWishart
#print axioms JinWishart.modifiedBesselI_nat_eq_factorialSeries
#print axioms JinWishart.modifiedBesselI_nat_ofReal_eq_realSeries
#print axioms JinWishart.nuttallQIntegrand_eq_evenRadialKernel
