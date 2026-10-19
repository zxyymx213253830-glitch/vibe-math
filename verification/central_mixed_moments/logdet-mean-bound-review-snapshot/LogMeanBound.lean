import JinWishartFormalization.FiniteSpectrumLogDetGrowth

/-! Log tangent inequality and finite-spectrum expectation bound.
Codex. [需人工审查] Integrability and expectation interpretation.
-/
open MeasureTheory
namespace JinWishart
noncomputable section

theorem log_tangent_upper_bound (y a : ℝ) (hy : 0 < y) (ha : 0 < a) :
    Real.log y ≤ Real.log a+y/a-1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy ha)
  rw [Real.log_div hy.ne' ha.ne'] at h
  linarith

theorem integral_log_tangent_upper_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hlog : Integrable (fun x => Real.log (f x)) μ) (a : ℝ) (ha : 0 < a) :
    (∫ x, Real.log (f x) ∂μ) ≤ Real.log a+(∫ x, f x ∂μ)/a-1 := by
  have hb : Integrable (fun x => Real.log a+f x/a-1) μ :=
    ((integrable_const _).add (hf.div_const a)).sub (integrable_const _)
  calc
    _ ≤ ∫ x, (Real.log a+f x/a-1) ∂μ :=
      integral_mono_ae hlog hb (hpos.mono (fun x hx => log_tangent_upper_bound (f x) a hx ha))
    _ = _ := by
      have hs := integral_sub ((integrable_const (Real.log a)).add (hf.div_const a))
        (integrable_const (1 : ℝ))
      have haint := integral_add (integrable_const (Real.log a)) (hf.div_const a)
      simp only [Pi.sub_apply,Pi.add_apply] at hs haint
      rw [hs,haint,integral_div]
      simp

theorem integral_finiteSpectrumLogDet_mean_upper_bound {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (hk : 0 < Fintype.card ι) (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hnonneg : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x) (r : ℝ) (hr : 0 ≤ r) :
    (∫ x, finiteSpectrumLogDet (fun i => f i x) r ∂μ) ≤
      (Fintype.card ι : ℝ)*Real.log (1+r*(∑ i, ∫ x, f i x ∂μ)/(Fintype.card ι : ℝ)) := by
  classical
  let K : ℝ := Fintype.card ι
  let T : ℝ := ∑ i, ∫ x, f i x ∂μ
  let a : ℝ := 1+r*T/K
  have hK : 0 < K := by change (0 : ℝ) < (Fintype.card ι : ℝ); exact_mod_cast hk
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae (hnonneg i))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hi (i : ι) := integrable_log_one_add_mul μ (f i) (hf i) (hnonneg i) r hr
  have hb (i : ι) : (∫ x, Real.log (1+r*f i x) ∂μ) ≤
      Real.log a+(1+r*(∫ x, f i x ∂μ))/a-1 := by
    have h := integral_log_tangent_upper_bound μ (fun x => 1+r*f i x)
      ((integrable_const _).add ((hf i).const_mul r))
      ((hnonneg i).mono (fun x hx => by positivity)) (hi i) a ha
    rw [integral_add (integrable_const (1 : ℝ)) ((hf i).const_mul r),integral_const_mul] at h
    simpa using h
  calc
    _ = ∑ i, ∫ x, Real.log (1+r*f i x) ∂μ := integral_finsetSum _ (fun i _ => hi i)
    _ ≤ ∑ i, (Real.log a+(1+r*(∫ x, f i x ∂μ))/a-1) :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by
      simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_div,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
      change K*Real.log a+(K*1+r*T)/a-K*1=K*Real.log a
      have he : (K+r*T)/a=K := by
        apply (div_eq_iff ha.ne').mpr
        dsimp only [a]
        field_simp [hK.ne']
        <;> ring
      simpa only [mul_one,he,add_sub_cancel_right]

end
end JinWishart
#print axioms JinWishart.log_tangent_upper_bound
#print axioms JinWishart.integral_log_tangent_upper_bound
#print axioms JinWishart.integral_finiteSpectrumLogDet_mean_upper_bound
