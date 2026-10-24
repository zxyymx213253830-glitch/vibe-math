import JinWishartFormalization.SymmetricTwoVariableOrderIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Codex. Seed2026102409 calibrated finite atomic moment/ordered-half controls.
Concrete two-variable moment determinant interface; no assumed determinant sign.
[需人工审查] Product integrability and ENNReal/Bochner conversion. -/
open MeasureTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

def twoMomentDeterminant (μ : Measure ℝ) : ℝ :=
  (∫ _ : ℝ,(1 : ℝ) ∂μ)*(∫ y : ℝ,y^2 ∂μ)-(∫ y : ℝ,y ∂μ)^2

theorem ordered_square_gap_moment_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h1 : Integrable (fun y : ℝ => y) μ) (h2 : Integrable (fun y : ℝ => y^2) μ) :
    0≤twoMomentDeterminant μ ∧
      (∫⁻ z in {z : ℝ × ℝ | z.2<z.1}, ENNReal.ofReal ((z.1-z.2)^2) ∂μ.prod μ)=
        ENNReal.ofReal (twoMomentDeterminant μ) := by
  have h0 : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hA := h2.mul_prod h0
  have hB := h0.mul_prod h2
  have hC := h1.mul_prod h1
  have hsum := (hA.add hB).sub (hC.const_mul 2)
  have hGap : Integrable (fun z : ℝ × ℝ => (z.1-z.2)^2) (μ.prod μ) :=
    hsum.congr (ae_of_all _ fun z => by ring)
  have hreal : (∫ z : ℝ × ℝ,(z.1-z.2)^2 ∂μ.prod μ)=2*twoMomentDeterminant μ := by
    calc
      _ = ∫ z : ℝ × ℝ,z.1^2*1+1*z.2^2-2*(z.1*z.2) ∂μ.prod μ :=
        integral_congr_ae (ae_of_all _ fun z => by ring)
      _ = (∫ z : ℝ × ℝ,z.1^2*1 ∂μ.prod μ)+(∫ z : ℝ × ℝ,1*z.2^2 ∂μ.prod μ)-
          2*(∫ z : ℝ × ℝ,z.1*z.2 ∂μ.prod μ) := by
        rw [integral_sub (hA.add hB) (hC.const_mul 2),integral_add hA hB,integral_const_mul]
      _ = _ := by
        rw [integral_prod_mul,integral_prod_mul,integral_prod_mul]
        unfold twoMomentDeterminant
        ring
  have hnonneg : 0≤twoMomentDeterminant μ := by
    have h := integral_nonneg (fun z : ℝ × ℝ => sq_nonneg (z.1-z.2)) (μ := μ.prod μ)
    rw [hreal] at h
    linarith
  refine ⟨hnonneg,?_⟩
  have hh := lintegral_symmetric_ordered_half μ
    (fun z => ENNReal.ofReal ((z.1-z.2)^2)) (by fun_prop)
    (fun x y => by congr 1;ring) (by intro x;simp)
  rw [← ofReal_integral_eq_lintegral_ofReal hGap (ae_of_all _ fun z => sq_nonneg (z.1-z.2)),
    hreal,ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)] at hh
  rw [← mul_assoc,show ENNReal.ofReal (2 : ℝ)=(2 : ℝ≥0∞) by norm_num,one_div,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠∞),one_mul] at hh
  exact hh

end
end JinWishart
#print axioms JinWishart.ordered_square_gap_moment_identity
