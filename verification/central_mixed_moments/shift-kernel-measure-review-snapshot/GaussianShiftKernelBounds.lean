import JinWishartFormalization.GaussianRawCoordinates

/-!
# Global Gaussian kernel comparison under a fixed mean shift

Codex proofs. These are pointwise density bounds; the measure comparison is
a separate obligation. Scale1/2 and2 are SOURCE standard deviations.
[需人工审查] Gaussian-density convention and future probability transport.
-/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem norm_sub_square_le_twice {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (x-y)) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

theorem gaussian_shift_exponent_bounds {E : Type*} [NormedAddCommGroup E] (x y : E) :
    -‖y‖^2-2*‖x‖^2 ≤ -‖x-y‖^2/2 ∧
    -‖x-y‖^2/2 ≤ ‖y‖^2-‖x‖^2/8 := by
  have h1 := norm_sub_square_le_twice x y
  have h2 := norm_sub_square_le_twice (x-y) (-y)
  simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at h2
  constructor <;> nlinarith [sq_nonneg ‖x‖,sq_nonneg ‖y‖]

theorem euclideanStdGaussianDensity_shift_bounds {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι) :
    Real.exp (-‖y‖^2)*euclideanStdGaussianDensity ((2 : ℝ) • x) ≤
        euclideanStdGaussianDensity (x-y) ∧
    euclideanStdGaussianDensity (x-y) ≤
        Real.exp (‖y‖^2)*euclideanStdGaussianDensity ((1/2 : ℝ) • x) := by
  have h := gaussian_shift_exponent_bounds x y
  have hnorm2 : ‖(2 : ℝ) • x‖^2 = 4*‖x‖^2 := by
    rw [norm_smul,Real.norm_eq_abs]; norm_num; ring
  have hnormhalf : ‖(1/2 : ℝ) • x‖^2 = ‖x‖^2/4 := by
    rw [norm_smul,Real.norm_eq_abs]; norm_num; ring
  have hc : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι := by positivity
  unfold euclideanStdGaussianDensity
  rw [hnorm2,hnormhalf]
  constructor
  · have he : Real.exp (-‖y‖^2)*Real.exp (-(4*‖x‖^2)/2) ≤
        Real.exp (-‖x-y‖^2/2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [h.1]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left he hc
  · have he : Real.exp (-‖x-y‖^2/2) ≤
        Real.exp (‖y‖^2)*Real.exp (-(‖x‖^2/4)/2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [h.2]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left he hc

end
end JinWishart
#print axioms JinWishart.norm_sub_square_le_twice
#print axioms JinWishart.gaussian_shift_exponent_bounds
#print axioms JinWishart.euclideanStdGaussianDensity_shift_bounds
