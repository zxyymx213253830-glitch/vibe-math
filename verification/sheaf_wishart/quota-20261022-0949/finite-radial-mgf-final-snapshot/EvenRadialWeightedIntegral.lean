import JinWishartFormalization.NaturalNuttallNormalization

/-! Codex. Seed2026102401 controls before source.
[需人工审查] Positive radial change of scale and weighted integrability.
Analytic kernel only; no actual general-row sample law is asserted. -/
open MeasureTheory Set
namespace JinWishart
noncomputable section

theorem evenRadialKernel_scaling (q : ℕ) (a r c : ℝ) (hc : 0<c) :
    c^(2*q+1)*Real.exp ((1-c^2)*r^2/2)*noncentralChiEvenRadialKernel q a r =
      Real.exp (a^2*(1-c^2)/(2*c^2))*noncentralChiEvenRadialKernel q (a/c) (c*r) := by
  have hn : c ≠ 0 := ne_of_gt hc
  have harg : (a/c)*(c*r)=a*r := by field_simp
  have he : Real.exp ((1-c^2)*r^2/2)*Real.exp (-((r^2+a^2)/2)) =
      Real.exp (a^2*(1-c^2)/(2*c^2))*Real.exp (-(((c*r)^2+(a/c)^2)/2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    <;> ring
  unfold noncentralChiEvenRadialKernel
  rw [harg, mul_pow]
  calc
    _ = (c^(2*q+1)*r^(2*q+1)/2^q) *
        (Real.exp ((1-c^2)*r^2/2)*Real.exp (-((r^2+a^2)/2))) *
        ∑' n : ℕ, ((a*r)^2/4)^n/((n.factorial : ℝ)*((n+q).factorial : ℝ)) := by ring
    _ = _ := by rw [he];ring

theorem evenRadialKernel_weighted_integral (q : ℕ) (a c : ℝ) (hc : 0<c) :
    (∫ r in Ioi (0 : ℝ), Real.exp ((1-c^2)*r^2/2)*noncentralChiEvenRadialKernel q a r) =
      Real.exp (a^2*(1-c^2)/(2*c^2))/c^(2*(q+1)) := by
  have hn : c ≠ 0 := ne_of_gt hc
  have hf : (fun r : ℝ => Real.exp ((1-c^2)*r^2/2)*noncentralChiEvenRadialKernel q a r) =
      fun r => (Real.exp (a^2*(1-c^2)/(2*c^2))/c^(2*q+1))*
        noncentralChiEvenRadialKernel q (a/c) (c*r) := by
    funext r
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (pow_ne_zero _ hn)).2
    simpa [div_mul_eq_mul_div, mul_assoc, mul_comm, mul_left_comm] using
      evenRadialKernel_scaling q a r c hc
  rw [hf, integral_const_mul, integral_comp_mul_left_Ioi _ 0 hc, mul_zero,
    noncentralChiEvenRadialKernel_integral_eq_one, smul_eq_mul, mul_one]
  rw [show 2*(q+1)=(2*q+1)+1 by omega, pow_succ]
  field_simp
  simp [pow_succ, mul_comm]

theorem evenRadialKernel_weighted_integrable (q : ℕ) (a c : ℝ) (hc : 0<c) :
    IntegrableOn (fun r : ℝ => Real.exp ((1-c^2)*r^2/2)*
      noncentralChiEvenRadialKernel q a r) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [evenRadialKernel_weighted_integral q a c hc]
  exact ne_of_gt (div_pos (Real.exp_pos _) (pow_pos hc _))

theorem evenRadialKernel_mgf_integral (q : ℕ) (a t : ℝ) (ht : t<1) :
    (∫ r in Ioi (0 : ℝ), Real.exp (t*r^2/2)*noncentralChiEvenRadialKernel q a r) =
      Real.exp (a^2*t/(2*(1-t)))/(1-t)^(q+1) := by
  have hp : 0<1-t := sub_pos.mpr ht
  have hs : (Real.sqrt (1-t))^2=1-t := Real.sq_sqrt hp.le
  have h := evenRadialKernel_weighted_integral q a (Real.sqrt (1-t)) (Real.sqrt_pos.2 hp)
  rw [show (Real.sqrt (1-t))^(2*(q+1))=((Real.sqrt (1-t))^2)^(q+1) by
    rw [pow_mul], hs, show 1-(1-t)=t by ring] at h
  exact h

theorem evenRadialKernel_mgf_integrable (q : ℕ) (a t : ℝ) (ht : t<1) :
    IntegrableOn (fun r : ℝ => Real.exp (t*r^2/2)*noncentralChiEvenRadialKernel q a r)
      (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [evenRadialKernel_mgf_integral q a t ht]
  exact ne_of_gt (div_pos (Real.exp_pos _) (pow_pos (sub_pos.mpr ht) _))

end
end JinWishart
#print axioms JinWishart.evenRadialKernel_scaling
#print axioms JinWishart.evenRadialKernel_weighted_integral
#print axioms JinWishart.evenRadialKernel_weighted_integrable
#print axioms JinWishart.evenRadialKernel_mgf_integral
#print axioms JinWishart.evenRadialKernel_mgf_integrable
