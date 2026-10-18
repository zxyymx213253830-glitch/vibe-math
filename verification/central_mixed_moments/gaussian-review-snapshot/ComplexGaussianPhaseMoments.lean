import JinWishartFormalization.GammaIntegerMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Circular complex Gaussian phase cancellation

Codex proof bodies. Actual variance-one Gaussian law, not an assumed density.
[需人工审查] Real isometry transport and complex Bochner integral convention.
-/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def standardComplexScalarLaw : Measure ℂ :=
  (stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)

instance isProbabilityMeasure_standardComplexScalarLaw : IsProbabilityMeasure standardComplexScalarLaw := by
  unfold standardComplexScalarLaw
  infer_instance

def complexUnitMulIsometry (c : ℂ) (hc : ‖c‖=1) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun := fun z => c*z
  invFun := fun z => c⁻¹*z
  left_inv := by
    have hn : c ≠ 0 := by intro h; simp [h] at hc
    intro z
    simp [← mul_assoc,hn]
  right_inv := by
    have hn : c ≠ 0 := by intro h; simp [h] at hc
    intro z
    simp [← mul_assoc,hn]
  map_add' := mul_add c
  map_smul' := by intro r z; simp [Algebra.smul_def,mul_left_comm,mul_assoc]
  norm_map' := by intro z; change ‖c*z‖=‖z‖; rw [norm_mul,hc,one_mul]

theorem standardComplexScalarLaw_map_unit (c : ℂ) (hc : ‖c‖=1) :
    standardComplexScalarLaw.map (fun z => c*z) = standardComplexScalarLaw := by
  have hu := stdGaussian_map (complexUnitMulIsometry c hc)
  have hU : (complexUnitMulIsometry c hc : ℂ → ℂ) = fun z => c*z := rfl
  rw [hU] at hu
  unfold standardComplexScalarLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun z : ℂ => c*z) ∘ (fun z => (Real.sqrt 2)⁻¹ • z) =
      (fun z => (Real.sqrt 2)⁻¹ • z) ∘ (fun z => c*z) := by
    funext z
    simp [Function.comp_def,Algebra.smul_def,mul_left_comm,mul_assoc]
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),hu]

def offDiagonalGaussianPhase (p q : ℕ) : ℂ :=
  Complex.exp (((Real.pi/((p : ℝ)-(q : ℝ)) : ℝ) : ℂ)*Complex.I)

theorem offDiagonalGaussianPhase_norm (p q : ℕ) : ‖offDiagonalGaussianPhase p q‖=1 := by
  unfold offDiagonalGaussianPhase
  rw [Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_zero,Real.exp_zero]

theorem offDiagonalGaussianPhase_factor (p q : ℕ) (hpq : p ≠ q) :
    (offDiagonalGaussianPhase p q)^p * star (offDiagonalGaussianPhase p q)^q = -1 := by
  have hd : (p : ℂ)-(q : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpq)
  unfold offDiagonalGaussianPhase
  rw [Complex.star_def,← Complex.exp_conj,← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul,← Complex.exp_add]
  rw [← Complex.exp_pi_mul_I]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  field_simp [hd]
  <;> ring

theorem integral_complexGaussian_monomial_offDiagonal (p q : ℕ) (hpq : p ≠ q) :
    (∫ z : ℂ, z^p * star z^q ∂standardComplexScalarLaw) = 0 := by
  let c := offDiagonalGaussianPhase p q
  have h := congrArg (fun μ => ∫ z : ℂ, z^p * star z^q ∂μ)
    (standardComplexScalarLaw_map_unit c (offDiagonalGaussianPhase_norm p q))
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  have he : (fun z : ℂ => (c*z)^p * star (c*z)^q) =
      fun z => (c^p * star c^q) * (z^p * star z^q) := by
    funext z
    simp only [mul_pow,star_mul]
    ring
  rw [he,integral_const_mul,offDiagonalGaussianPhase_factor p q hpq] at h
  have h2 : (2 : ℂ)*(∫ z : ℂ, z^p * star z^q ∂standardComplexScalarLaw) = 0 := by
    linear_combination -h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

end
end JinWishart
#print axioms JinWishart.isProbabilityMeasure_standardComplexScalarLaw
#print axioms JinWishart.standardComplexScalarLaw_map_unit
#print axioms JinWishart.offDiagonalGaussianPhase_norm
#print axioms JinWishart.offDiagonalGaussianPhase_factor
#print axioms JinWishart.integral_complexGaussian_monomial_offDiagonal
