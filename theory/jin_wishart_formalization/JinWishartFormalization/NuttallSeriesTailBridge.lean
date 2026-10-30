import JinWishartFormalization.QuadraticEnergyTailChange
import JinWishartFormalization.MixedKernelMoments
import JinWishartFormalization.BesselProductKernel
import JinWishartFormalization.NoncentralRadialFullMoments

/-! Codex. Seed 2026103006:531 numerical Nuttall/Gamma matrix bridge checks
precede this source. This is a scalar formula-side bridge, not actual spectral
law identification. [需人工审查] Jacobian, Bessel conventions and endpoints. -/
open MeasureTheory Set
namespace JinWishart
noncomputable section

theorem nuttall_series_integrand_re (q k : ℕ) (lambda r : ℝ)
 (hl : 0 ≤ lambda) (hr : 0 ≤ r) :
 (nuttallQIntegrand (q+2*k+1) q (Real.sqrt (2*lambda)) r).re =
 ((Real.sqrt 2)^q * 2^k) * (Real.sqrt lambda)^q * Real.exp (-lambda) *
   (r*((r^2/2)^(q+k)*Real.exp (-(r^2/2))*scalarSeriesKernel q lambda (r^2/2))) := by
 let y : ℝ := r^2/2
 have hy : 0 ≤ y := by dsimp [y]; positivity
 have hs2 : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
 have hsy : (Real.sqrt y)^2 = y := Real.sq_sqrt hy
 have hsl : (Real.sqrt (2*lambda))^2 = 2*lambda := Real.sq_sqrt (by positivity)
 have hsyl : (Real.sqrt (y*lambda))^2 = y*lambda := Real.sq_sqrt (mul_nonneg hy hl)
 have hroot : Real.sqrt 2 * Real.sqrt y = r := by
   rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
   rw [show 2*y = r^2 by dsimp [y]; ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
 have harg : Real.sqrt (2*lambda)*r = 2*Real.sqrt (y*lambda) := by
   rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),Real.sqrt_mul hy]
   calc
     _ = Real.sqrt lambda*(Real.sqrt 2*r) := by ring
     _ = Real.sqrt lambda*(2*Real.sqrt y) := by
       rw [← hroot]
       have ht : Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt y) = 2 * Real.sqrt y := by
         calc
           _ = (Real.sqrt 2)^2 * Real.sqrt y := by ring
           _ = _ := by rw [hs2]
       rw [ht]
     _ = _ := by ring
 have hrootPow : (Real.sqrt 2)^q * (Real.sqrt y)^q = r^q := by
   rw [← mul_pow,hroot]
 have hrpow : r^(2*k) = (2 : ℝ)^k*y^k := by
   calc
     _ = (r^2)^k := by rw [pow_mul]
     _ = _ := by rw [show r^2 = 2*y by dsimp [y]; ring,mul_pow]
 have hpowr : r^q * (Real.sqrt y)^q = (Real.sqrt 2)^q*y^q := by
   rw [← hrootPow]
   calc
     _ = (Real.sqrt 2)^q*((Real.sqrt y)^q*(Real.sqrt y)^q) := by ring
     _ = _ := by rw [← mul_pow,← pow_two,hsy]
 have hpow : r^(q+2*k+1)*(Real.sqrt y)^q =
     ((Real.sqrt 2)^q*(2 : ℝ)^k)*(r*y^(q+k)) := by
   calc
     _ = r*r^(2*k)*(r^q*(Real.sqrt y)^q) := by rw [pow_add,pow_add,pow_one]; ring
     _ = _ := by rw [hrpow,hpowr,pow_add]; ring
 have hexp : Real.exp (-((r^2+(Real.sqrt (2*lambda))^2)/2)) =
     Real.exp (-y)*Real.exp (-lambda) := by
   rw [hsl,← Real.exp_add]
   congr 1
   dsimp [y]
   ring
 have hb := modifiedBesselI_sqrt_product_re q y lambda hy hl
 rw [← harg] at hb
 change (modifiedBesselI q ((Real.sqrt (2*lambda)*r : ℝ) : ℂ)).re =
   (Real.sqrt y)^q*((Real.sqrt lambda)^q*scalarSeriesKernel q lambda y) at hb
 simp only [nuttallQIntegrand,← Complex.ofReal_pow,← Complex.ofReal_mul,
   Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
 rw [hexp,hb]
 change r^(q+2*k+1) * (Real.exp (-y)*Real.exp (-lambda)) *
   ((Real.sqrt y)^q*((Real.sqrt lambda)^q*scalarSeriesKernel q lambda y)) = _
 rw [show r^(q+2*k+1) * (Real.exp (-y)*Real.exp (-lambda)) *
   ((Real.sqrt y)^q*((Real.sqrt lambda)^q*scalarSeriesKernel q lambda y)) =
   (r^(q+2*k+1)*(Real.sqrt y)^q)*
     (Real.exp (-y)*Real.exp (-lambda)*(Real.sqrt lambda)^q*scalarSeriesKernel q lambda y) by ring,
   hpow]
 dsimp [y]
 ring

theorem nuttallQ_series_tail_re (q k : ℕ) (lambda x : ℝ)
 (hl : 0 ≤ lambda) (hx : 0 ≤ x) :
 (nuttallQ (q+2*k+1) q (Real.sqrt (2*lambda)) (Real.sqrt (2*x))).re =
 ((Real.sqrt 2)^q * 2^k) * (Real.sqrt lambda)^q * Real.exp (-lambda) *
   (∫ y in Ioi x, y^(q+k)*Real.exp (-y)*scalarSeriesKernel q lambda y) := by
 let a := Real.sqrt (2*x)
 have ha : 0 ≤ a := Real.sqrt_nonneg _
 have ha2 : a^2/2 = x := by
   dsimp [a]
   rw [Real.sq_sqrt (by positivity)]
   ring
 have hint : IntegrableOn (nuttallQIntegrand (q+2*k+1) q (Real.sqrt (2*lambda))) (Ioi a) :=
   (integrableOn_nuttallQ_fullNaturalMoment q k (Real.sqrt (2*lambda))).mono_set (Ioi_subset_Ioi ha)
 have hre : (nuttallQ (q+2*k+1) q (Real.sqrt (2*lambda)) a).re =
     ∫ r in Ioi a, (nuttallQIntegrand (q+2*k+1) q (Real.sqrt (2*lambda)) r).re := by
   unfold nuttallQ
   exact (integral_re hint).symm
 change (nuttallQ (q+2*k+1) q (Real.sqrt (2*lambda)) a).re = _
 rw [hre]
 calc
   _ = ∫ r in Ioi a, (((Real.sqrt 2)^q * 2^k) * (Real.sqrt lambda)^q * Real.exp (-lambda)) *
       (r*((r^2/2)^(q+k)*Real.exp (-(r^2/2))*scalarSeriesKernel q lambda (r^2/2))) := by
     apply setIntegral_congr_fun measurableSet_Ioi
     intro r hr
     exact nuttall_series_integrand_re q k lambda r hl (le_of_lt (lt_of_le_of_lt ha hr))
   _ = (((Real.sqrt 2)^q * 2^k) * (Real.sqrt lambda)^q * Real.exp (-lambda)) *
       (∫ r in Ioi a, r*((r^2/2)^(q+k)*Real.exp (-(r^2/2))*scalarSeriesKernel q lambda (r^2/2))) :=
       integral_const_mul _ _
   _ = _ := by
     have h := quadraticEnergy_tail_substitution a ha
       (fun y => y^(q+k)*Real.exp (-y)*scalarSeriesKernel q lambda y)
     rw [ha2] at h
     rw [← h]

theorem paperScaled_nuttallQ_series_tail_re (q k : ℕ) (lambda x : ℝ)
 (hl : 0 ≤ lambda) (hx : 0 ≤ x) :
 Real.rpow 2 (-((q : ℝ)/2)-(k : ℝ)) *
   (nuttallQ (q+2*k+1) q (Real.sqrt (2*lambda)) (Real.sqrt (2*x))).re =
 (Real.sqrt lambda)^q * Real.exp (-lambda) *
   (∫ y in Ioi x, y^(q+k)*Real.exp (-y)*scalarSeriesKernel q lambda y) := by
 have hc : (Real.sqrt 2)^q * (2 : ℝ)^k = Real.rpow 2 ((q : ℝ)/2+(k : ℝ)) := by
   rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul (by norm_num),
     ← Real.rpow_natCast,← Real.rpow_add (by norm_num)]
   congr 1
   ring
 have hcancel : Real.rpow 2 (-((q : ℝ)/2)-(k : ℝ)) *
     ((Real.sqrt 2)^q * (2 : ℝ)^k) = 1 := by
   rw [hc]
   change (2 : ℝ)^(-((q : ℝ)/2)-(k : ℝ)) *
     (2 : ℝ)^((q : ℝ)/2+(k : ℝ)) = 1
   rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
   have he : -((q : ℝ)/2)-(k : ℝ)+((q : ℝ)/2+(k : ℝ)) = 0 := by ring
   rw [he,Real.rpow_zero]
 rw [nuttallQ_series_tail_re q k lambda x hl hx]
 calc
   _ = (Real.rpow 2 (-((q : ℝ)/2)-(k : ℝ)) *
       ((Real.sqrt 2)^q * (2 : ℝ)^k)) *
       ((Real.sqrt lambda)^q * Real.exp (-lambda) *
         (∫ y in Ioi x, y^(q+k)*Real.exp (-y)*scalarSeriesKernel q lambda y)) := by ring
   _ = _ := by rw [hcancel,one_mul]

theorem nuttallQ_natural_tail_im_zero (q k : ℕ) (a b : ℝ) (hb : 0 ≤ b) :
 (nuttallQ (q+2*k+1) q a b).im = 0 := by
 have hi : IntegrableOn (nuttallQIntegrand (q+2*k+1) q a) (Ioi b) :=
   (integrableOn_nuttallQ_fullNaturalMoment q k a).mono_set (Ioi_subset_Ioi hb)
 unfold nuttallQ
 change RCLike.im (∫ t in Ioi b, nuttallQIntegrand (q+2*k+1) q a t) = 0
 rw [← integral_im hi]
 have hz (r : ℝ) : (nuttallQIntegrand (q+2*k+1) q a r).im = 0 := by
   rw [nuttallQIntegrand,← modifiedBesselI_nat_ofReal_eq_realSeries]
   simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_im]
 simp [hz]

theorem paperScaled_nuttallQ_series_tail (q k : ℕ) (lambda x : ℝ)
 (hl : 0 ≤ lambda) (hx : 0 ≤ x) :
 (Real.rpow 2 (-((q : ℝ)/2)-(k : ℝ)) : ℂ) *
   nuttallQ (q+2*k+1) q (Real.sqrt (2*lambda)) (Real.sqrt (2*x)) =
 ((Real.sqrt lambda)^q * Real.exp (-lambda) *
   (∫ y in Ioi x, y^(q+k)*Real.exp (-y)*scalarSeriesKernel q lambda y) : ℝ) := by
 have hi := nuttallQ_natural_tail_im_zero q k (Real.sqrt (2*lambda))
   (Real.sqrt (2*x)) (Real.sqrt_nonneg _)
 apply Complex.ext
 · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
   exact paperScaled_nuttallQ_series_tail_re q k lambda x hl hx
 · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,hi,mul_zero]

end
end JinWishart
#print axioms JinWishart.nuttall_series_integrand_re
#print axioms JinWishart.nuttallQ_series_tail_re
#print axioms JinWishart.paperScaled_nuttallQ_series_tail_re
#print axioms JinWishart.nuttallQ_natural_tail_im_zero
#print axioms JinWishart.paperScaled_nuttallQ_series_tail
