import JinWishartFormalization.SphereFourDPlaneAngleChart
import JinWishartFormalization.NuttallQ21Normalization

/-!
# Radial integration interface for the noncentral four-dimensional model

This module collects the radius-measure reductions needed to turn the proved
four-dimensional Gaussian shell identity into a ball probability and then a
`Q_{2,1}` tail formula.
-/

open MeasureTheory Set

namespace JinWishart

/-- Unfolding `volumeIoiPow 3` exposes the four-dimensional radial Jacobian
as an ordinary Lebesgue integral with weight `r^3`. -/
theorem integral_volumeIoiPow_three_eq_Ioi (f : Ioi (0 : ℝ) → ℝ) :
    (∫ r, f r ∂(Measure.volumeIoiPow 3)) =
      ∫ r : Ioi (0 : ℝ), (r : ℝ) ^ 3 * f r
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    funext r
    have hr : 0 < (r : ℝ) := r.property
    simp only [ENNReal.toReal_ofReal (pow_nonneg hr.le 3)]
    simp [smul_eq_mul]
  · fun_prop
  · filter_upwards with r
    simp

/-- The four-dimensional noncentral radial kernel is integrable and has total
mass one for every positive noncentrality amplitude. -/
theorem noncentralChiFourRadialKernel_integrableOn_Ioi
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (noncentralChiFourRadialKernel a) (Ioi (0 : ℝ)) := by
  have hreal := nuttallQ21RealKernel_integrableOn_Ioi a ha.le
  have hfun : (fun r : ℝ => noncentralChiFourRadialKernel a r) =
      fun r => a⁻¹ * nuttallQ21RealKernel a r := by
    funext r
    simp [noncentralChiFourRadialKernel, nuttallQ21RealKernel]
    field_simp [ha.ne']
  apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2
    (hreal.const_mul (a⁻¹))
  intro r _
  exact congrFun hfun r

theorem noncentralChiFourRadialKernel_integral_eq_one
    (a : ℝ) (ha : 0 < a) :
    ∫ r in Ioi (0 : ℝ), noncentralChiFourRadialKernel a r = 1 := by
  have hfun : (fun r : ℝ => noncentralChiFourRadialKernel a r) =
      fun r => a⁻¹ * nuttallQ21RealKernel a r := by
    funext r
    simp [noncentralChiFourRadialKernel, nuttallQ21RealKernel]
    field_simp [ha.ne']
  rw [hfun, integral_const_mul, nuttallQ21RealIntegral_eq_amplitude a ha]
  field_simp [ha.ne']

end JinWishart
