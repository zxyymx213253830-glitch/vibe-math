import JinWishartFormalization.GaussianEvenRadialLaw
import JinWishartFormalization.NoncentralOneColumnEnergy
import JinWishartFormalization.OneColumnRadialCDF
import JinWishartFormalization.OneColumnFrobeniusParameter

/-! Codex. Seed2026102402 controls before source.
[需人工审查] Radial energy sublevel, physical CN1 scaling and original T1/T2.
All positive row counts; zero means allowed for radial CDF, nonzero for L=1 formulas. -/
open MeasureTheory ProbabilityTheory Set
namespace JinWishart
noncomputable section

theorem evenRadialMeasure_energyCDF (q : ℕ) (a x : ℝ) (hx : 0≤x) :
    cdf ((evenRadialMeasure q a).map (fun r : ℝ => r^2/2)) x =
      ∫ r in Ioc (0 : ℝ) (Real.sqrt (2*x)), noncentralChiEvenRadialKernel q a r := by
  have hs : MeasurableSet ((fun r : ℝ => r^2/2) ⁻¹' Iic x) :=
    measurableSet_Iic.preimage (by fun_prop)
  have hset : ((fun r : ℝ => r^2/2) ⁻¹' Iic x) ∩ Ioi 0 = Ioc 0 (Real.sqrt (2*x)) := by
    ext r
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_Ioc]
    have hR := Real.sqrt_nonneg (2*x)
    have hR2 := Real.sq_sqrt (show 0≤2*x by positivity)
    constructor
    · rintro ⟨he,hr⟩
      exact ⟨hr, by nlinarith⟩
    · rintro ⟨hr,he⟩
      exact ⟨by nlinarith,hr⟩
  rw [cdf_eq_real, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic]
  unfold evenRadialMeasure
  rw [withDensity_apply _ hs, Measure.restrict_restrict hs, hset]
  have hI : IntegrableOn (noncentralChiEvenRadialKernel q a)
      (Ioc 0 (Real.sqrt (2*x))) :=
    (integrableOn_noncentralChiEvenRadialKernel q a).mono_set (fun _ hr => hr.1)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (Real.sqrt (2*x)))] noncentralChiEvenRadialKernel q a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    unfold noncentralChiEvenRadialKernel
    apply mul_nonneg
    · exact mul_nonneg (div_nonneg (pow_nonneg (le_of_lt hr.1) _) (by positivity)) (Real.exp_pos _).le
    · exact tsum_nonneg (fun n => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]

theorem noncentralColumnCDF_eq_generalRadialIntegral {m : ℕ} (hm : 0<m)
    (M : Matrix (Fin m) (Fin 1) ℂ) (x : ℝ) (hx : 0≤x) :
    cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
    ∫ r in Ioc (0 : ℝ) (Real.sqrt (2*x)),
      noncentralChiEvenRadialKernel (m-1) ‖complexSampleMean M‖ r := by
  have hd : Fintype.card (((Fin m × Fin 1) × Fin 2))=2*((m-1)+1) := by simp;omega
  have hLaw := stdGaussian_energy_eq_evenRadialLaw (m-1) hd (complexSampleMean M)
  have hf : complexNoncentralSampleSmallestEigenvalue M (by norm_num) =
      fun z => ‖z+complexSampleMean M‖^2/2 :=
    funext (complexNoncentralColumnSmallestEigenvalue_eq_shiftedEnergy hm M)
  rw [hf,hLaw,evenRadialMeasure_energyCDF _ _ _ hx]

theorem theorem12OneColumnCandidates_eq_actualCDF_frobenius {m : ℕ} (hm : 0<m)
    (M : Matrix (Fin m) (Fin 1) ℂ) (x : ℝ)
    (hEnergy : 0<∑ i : Fin m,‖M i 0‖^2) (hx : 0≤x) :
    let lambda := ∑ i : Fin m,‖M i 0‖^2
    let F := cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x
    theorem1CdfCandidate 1 m 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x=F ∧
      theorem2CdfCandidate 1 m 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x=F := by
  intro lambda F
  have h := theorem12OneColumnCandidates_eq_radialCDF m (by omega) lambda x hEnergy hx
  have hn : ‖complexSampleMean M‖=Real.sqrt (2*lambda) := by
    have hsq := complexSampleMean_oneColumn_norm_sq_eq_twice_frobenius M
    change ‖complexSampleMean M‖^2=2*lambda at hsq
    rw [← hsq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hF : F=∫ r in Ioc (0 : ℝ) (Real.sqrt (2*x)),
      noncentralChiEvenRadialKernel (m-1) (Real.sqrt (2*lambda)) r := by
    dsimp only [F]
    rw [noncentralColumnCDF_eq_generalRadialIntegral hm M x hx,hn]
  exact ⟨h.1.trans hF.symm,h.2.trans hF.symm⟩

end
end JinWishart
#print axioms JinWishart.evenRadialMeasure_energyCDF
#print axioms JinWishart.noncentralColumnCDF_eq_generalRadialIntegral
#print axioms JinWishart.theorem12OneColumnCandidates_eq_actualCDF_frobenius
