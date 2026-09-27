import JinWishartFormalization.SphereFourDPlaneAngleChart
import JinWishartFormalization.NuttallQ21Normalization
import JinWishartFormalization.NoncentralFourDimensionalTail

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

/-- The complex Nuttall-Q integrand inherits positive-half-line
integrability from its equal real Bessel kernel. -/
theorem nuttallQ21Integrand_integrableOn_Ioi (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (nuttallQIntegrand 2 1 a) (Ioi (0 : ℝ)) := by
  have hreal := nuttallQ21RealKernel_integrableOn_Ioi a ha
  have hcomplex : IntegrableOn
      (fun r : ℝ => (nuttallQ21RealKernel a r : ℂ)) (Ioi (0 : ℝ)) :=
    Complex.ofRealCLM.integrable_comp hreal
  apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 hcomplex
  intro r _
  exact nuttallQ21Integrand_eq_realKernel a r

/-- The actual axial Gaussian radial kernel's upper tail is the normalized
`Q_{2,1}` tail, without an extra integrability assumption. -/
theorem noncentralChiFourRadialTail_eq_nuttallQ21_div_of_nonneg
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ r in Ioi b, noncentralChiFourRadialKernel a r) =
      (nuttallQ 2 1 a b / (a : ℂ)).re := by
  apply JinWishart.noncentralChiFourRadialTail_eq_nuttallQ21_div a b ha
  exact (nuttallQ21Integrand_integrableOn_Ioi a ha.le).mono_set
    (Ioi_subset_Ioi hb)

/-- The radial mass inside a nonnegative threshold is one minus the normalized
`Q_{2,1}` tail. This is the CDF identity for the already-derived radial law. -/
theorem noncentralChiFourRadialLowerMass_eq_one_sub_nuttallQ21
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ r in Ioc (0 : ℝ) b, noncentralChiFourRadialKernel a r) =
      1 - (nuttallQ 2 1 a b / (a : ℂ)).re := by
  have htotal : (∫ r : ℝ, noncentralChiFourRadialKernel a r
      ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ))) = 1 := by
    simpa only [] using noncentralChiFourRadialKernel_integral_eq_one a ha
  have htail := noncentralChiFourRadialTail_eq_nuttallQ21_div_of_nonneg
    a b ha hb
  have hupper : Ioi (0 : ℝ) ∩ Ioi b = Ioi b := by
    ext r
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro hr
      exact ⟨lt_of_le_of_lt hb hr, hr⟩
  have hlower : Ioi (0 : ℝ) ∩ (Ioi b)ᶜ = Ioc (0 : ℝ) b := by
    ext r
    simp [mem_inter_iff, mem_Ioi, mem_compl_iff, mem_Ioc]
  have hpart := setIntegral_compl (μ := (volume : Measure ℝ).restrict
      (Ioi (0 : ℝ))) (s := Ioi b) measurableSet_Ioi
      (noncentralChiFourRadialKernel_integrableOn_Ioi a ha)
  have htailRestrict :
      (∫ r in Ioi b, noncentralChiFourRadialKernel a r
        ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ))) =
        (nuttallQ 2 1 a b / (a : ℂ)).re := by
    change (∫ r, noncentralChiFourRadialKernel a r
      ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).restrict (Ioi b)) = _
    rw [Measure.restrict_restrict measurableSet_Ioi, Set.inter_comm, hupper]
    exact htail
  have hlowerRestrict :
      (∫ r in (Ioi b)ᶜ, noncentralChiFourRadialKernel a r
        ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ))) =
        (∫ r in Ioc (0 : ℝ) b, noncentralChiFourRadialKernel a r) := by
    change (∫ r, noncentralChiFourRadialKernel a r
      ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).restrict (Ioi b)ᶜ) = _
    rw [Measure.restrict_restrict measurableSet_Ioi.compl, Set.inter_comm, hlower]
  calc
    _ = ∫ r in (Ioi b)ᶜ, noncentralChiFourRadialKernel a r
        ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)) := hlowerRestrict.symm
    _ = 1 - (nuttallQ 2 1 a b / (a : ℂ)).re := by
      rw [hpart, htotal, htailRestrict]

end JinWishart
