import JinWishartFormalization.NoncentralFourDimensionalRadial

/-!
# Four-dimensional radial tail as normalized `Q_{2,1}`

The theorem below is the analytic tail identity for the candidate radial
kernel.  The remaining geometric obligation is to prove that the actual
shifted Gaussian pushforward has this radial density using the S³
surface-coordinate chart.
-/

open MeasureTheory Set

namespace JinWishart

theorem noncentralChiFourRadialTail_eq_nuttallQ21_div
    (a b : ℝ) (ha : 0 < a)
    (hint : IntegrableOn (fun r : ℝ => nuttallQIntegrand 2 1 a r) (Ioi b)) :
    (∫ r in Ioi b, noncentralChiFourRadialKernel a r) =
      (nuttallQ 2 1 a b / (a : ℂ)).re := by
  have hpoint (r : ℝ) :
      noncentralChiFourRadialKernel a r =
        (nuttallQIntegrand 2 1 a r).re / a := by
    have h := congrArg Complex.re
      (noncentralChiFourRadialKernel_eq_nuttallQ21_div a r ha.ne')
    simpa only [Complex.ofReal_re, Complex.div_ofReal_re] using h
  have hfun : (fun r : ℝ => noncentralChiFourRadialKernel a r) =
      fun r => a⁻¹ * (nuttallQIntegrand 2 1 a r).re := by
    funext r
    rw [hpoint]
    field_simp [ha.ne']
  have hre :
      (∫ r in Ioi b, (nuttallQIntegrand 2 1 a r).re) =
        (∫ r in Ioi b, nuttallQIntegrand 2 1 a r).re := by
    simpa using (integral_re
      (μ := volume.restrict (Ioi b)) hint)
  rw [hfun, integral_const_mul]
  unfold nuttallQ
  rw [Complex.div_ofReal_re]
  rw [← hre]
  ring

end JinWishart
