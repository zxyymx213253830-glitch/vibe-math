import JinWishartFormalization.OneColumnNuttallNormalization

/-! Literal one-column candidates equal the normalized radial lower integral.
Codex. Seed2026102250 CDF/source controls before source.
[需人工审查] Half-line partition, nonnegativity and paper parameter matching.
Actual Gaussian-law identification is separate from this analytic statement. -/
open MeasureTheory Set
namespace JinWishart
noncomputable section

private theorem evenKernelNonneg (q : ℕ) (a r : ℝ) (hr : 0≤r) :
    0≤noncentralChiEvenRadialKernel q a r := by
  unfold noncentralChiEvenRadialKernel
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg (pow_nonneg hr _) (by positivity)) (Real.exp_pos _).le
  · exact tsum_nonneg (fun n => by positivity)

theorem nuttallQ_succ_self_tail_norms (q : ℕ) (a b : ℝ) (ha : 0<a) (hb : 0≤b) :
    let L := ∫ r in Ioc (0 : ℝ) b,noncentralChiEvenRadialKernel q a r
    ‖nuttallQ (q+1) q a b‖=a^q*(1-L) ∧
      ‖(a : ℂ)^q-nuttallQ (q+1) q a b‖=a^q*L := by
  intro L
  let K := noncentralChiEvenRadialKernel q a
  let T := ∫ r in Ioi b,K r
  have hI : IntegrableOn K (Ioi 0) := integrableOn_noncentralChiEvenRadialKernel q a
  have hIb : IntegrableOn K (Ioi b) := hI.mono_set (Ioi_subset_Ioi hb)
  have hs : L+T=1 := by
    have hh := intervalIntegral.integral_interval_add_Ioi (a := (0 : ℝ)) (b := b) hI hIb
    rw [intervalIntegral.integral_of_le hb] at hh
    exact hh.trans (noncentralChiEvenRadialKernel_integral_eq_one q a)
  have hLn : 0≤L := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact evenKernelNonneg q a r hr.1.le
  have hTn : 0≤T := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact evenKernelNonneg q a r (hb.trans hr.le)
  have hQ : nuttallQ (q+1) q a b=((a^q*T : ℝ) : ℂ) := by
    unfold nuttallQ
    have hf : nuttallQIntegrand (q+1) q a=
        fun r : ℝ => (a : ℂ)^q*(K r : ℂ) :=
      funext (nuttallQIntegrand_eq_evenRadialKernel q a)
    rw [hf,integral_const_mul,integral_complex_ofReal]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,T]
  have hTL : T=1-L := by linarith
  constructor
  · rw [hQ,Complex.norm_of_nonneg (mul_nonneg (pow_nonneg ha.le _) hTn),hTL]
  · have hd : (a : ℂ)^q-nuttallQ (q+1) q a b=((a^q*L : ℝ) : ℂ) := by
      rw [hQ,hTL]
      push_cast
      ring
    rw [hd,Complex.norm_of_nonneg (mul_nonneg (pow_nonneg ha.le _) hLn)]

theorem theorem12OneColumnCandidates_eq_radialCDF
    (t : ℕ) (ht : 1≤t) (lambda x : ℝ) (hl : 0<lambda) (hx : 0≤x) :
    let L := ∫ r in Ioc (0 : ℝ) (Real.sqrt (2*x)),
      noncentralChiEvenRadialKernel (t-1) (Real.sqrt (2*lambda)) r
    theorem1CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x=L ∧
      theorem2CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x=L := by
  intro L
  have ha : 0<Real.sqrt (2*lambda) := Real.sqrt_pos.mpr (by positivity)
  have hn := nuttallQ_succ_self_tail_norms (t-1) (Real.sqrt (2*lambda))
    (Real.sqrt (2*x)) ha (Real.sqrt_nonneg _)
  have ht' : t-1+1=t := Nat.sub_add_cancel ht
  rw [ht'] at hn
  have hpow : (Real.sqrt (2*lambda))^(t-1)≠0 := pow_ne_zero _ ha.ne'
  constructor
  · rw [theorem1OneColumnCandidate_eq_explicitNormalizedQ t ht lambda x hl]
    unfold theorem1OneColumnNuttallQ
    rw [hn.1,mul_div_cancel_left₀ _ hpow]
    ring
  · rw [theorem2OneColumnCandidate_eq_explicitNormalizedQ t ht lambda x hl]
    unfold theorem1OneColumnNuttallQ
    rw [hn.2,mul_div_cancel_left₀ _ hpow]

end
end JinWishart
#print axioms JinWishart.nuttallQ_succ_self_tail_norms
#print axioms JinWishart.theorem12OneColumnCandidates_eq_radialCDF
