import JinWishartFormalization.CentralBartlettCoordinateJacobian
import JinWishartFormalization.GaussianBartlettGramDeterminant
import JinWishartFormalization.GaussianGramSupport

/-!
# Determinant, trace, cone and explicit normalization for density induction

Codex proofs. Finite product normalization is pi^(-n(n-1)/2) divided by
the factorial product (d+j)!, j=0,...,n-1. This file is deterministic algebra;
the actual probability-law induction is a separate obligation.
[需人工审查] Coordinate and variance correspondence with the actual density.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem complexVectorGramRankOne_trace {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    (complexVectorGramRankOne z).trace = (‖z‖ : ℂ) ^ 2 := by
  change (∑ i : Fin n, star (z i) * z i) = (‖z‖ : ℂ) ^ 2
  rw [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [RCLike.star_def, mul_comm] using (RCLike.mul_conj (z i))

theorem centralBartlettGram_trace {n : ℕ} (r : ℝ) (z : EuclideanSpace ℂ (Fin n))
    (B : Matrix (Fin n) (Fin n) ℂ) :
    (centralBartlettGram r z B).trace = (r : ℂ) + (‖z‖ : ℂ) ^ 2 + B.trace := by
  have h : (centralBartlettGram r z B).trace = (r : ℂ) +
      B.trace + (complexVectorGramRankOne z).trace := by
    simp [Matrix.trace, centralBartlettGram, complexVectorGramRankOne,
      Fin.sum_univ_succ, Finset.sum_add_distrib, add_assoc]
  rw [h, complexVectorGramRankOne_trace]
  ring

theorem centralBartlettGram_isHermitian {n : ℕ} (r : ℝ) (z : EuclideanSpace ℂ (Fin n))
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian) :
    (centralBartlettGram r z B).IsHermitian := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [Matrix.conjTranspose_apply, centralBartlettGram, star_mul,
    hB.apply, mul_comm]

theorem centralBartlettGram_posDef_iff {n : ℕ} (r : ℝ) (hr : 0 < r)
    (z : EuclideanSpace ℂ (Fin n)) (B : Matrix (Fin n) (Fin n) ℂ) :
    (centralBartlettGram r z B).PosDef ↔ B.PosDef := by
  let A : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of (fun _ _ => (r : ℂ))
  have hA : A.PosDef := by
    have hd : A = Matrix.diagonal (fun _ : Fin 1 => (r : ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hd]
    exact Matrix.PosDef.diagonal (fun _ => by exact_mod_cast hr)
  have he : (centralBartlettGram r z B).PosDef ↔
      ((centralBartlettGram r z B).submatrix (centralBartlettIndexEquiv n)
        (centralBartlettIndexEquiv n)).PosDef := by
    constructor
    · intro h
      exact h.submatrix (centralBartlettIndexEquiv n).injective
    · intro h
      have hb := h.submatrix (centralBartlettIndexEquiv n).symm.injective
      have hm : ((centralBartlettGram r z B).submatrix (centralBartlettIndexEquiv n)
          (centralBartlettIndexEquiv n)).submatrix (centralBartlettIndexEquiv n).symm
            (centralBartlettIndexEquiv n).symm = centralBartlettGram r z B := by
        ext i j
        simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
      rw [hm] at hb
      exact hb
  rw [he, centralBartlettGram_block_factor r hr, centralBlockStep_posDef_iff]
  change (Matrix.fromBlocks A 0 0 B).PosDef ↔ B.PosDef
  constructor
  · intro h
    have hb := h.submatrix (e := Sum.inr) Sum.inr_injective
    have hm : (Matrix.fromBlocks A 0 0 B).submatrix Sum.inr Sum.inr = B := by
      ext i j
      rfl
    rw [hm] at hb
    exact hb
  · intro hB
    letI := hA.isUnit.invertible
    have hpsd : (Matrix.fromBlocks A 0 0 B).PosSemidef := by
      have hh := Matrix.PosDef.fromBlocks₁₁ (0 : Matrix (Fin 1) (Fin n) ℂ) B hA
      simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, sub_zero] at hh
      exact hh.mpr hB.posSemidef
    apply hpsd.posDef_iff_det_ne_zero.mpr
    rw [Matrix.det_fromBlocks_zero₂₁]
    exact mul_ne_zero hA.det_pos.ne' hB.det_pos.ne'

theorem hermitianOfRealCoordinates_centralChart {n : ℕ} (r : ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) :
    hermitianOfRealCoordinates (centralBartlettCoordinateChart (r, (z, Q))) =
      centralBartlettGram r z (hermitianOfRealCoordinates Q) := by
  rw [centralBartlettCoordinateChart_eq_realGram]
  exact hermitianOfRealCoordinates_realCoordinates _
    (centralBartlettGram_isHermitian r z _ (hermitianOfRealCoordinates_isHermitian Q))

def centralWishartDensityConstant (d n : ℕ) : ℝ :=
  ∏ j : Fin n, (Real.pi⁻¹) ^ j.val * ((Nat.factorial (d + j.val) : ℕ) : ℝ)⁻¹

theorem centralWishartDensityConstant_pos (d n : ℕ) : 0 < centralWishartDensityConstant d n := by
  apply Finset.prod_pos
  intro j _
  positivity

theorem centralWishartDensityConstant_succ (d n : ℕ) :
    centralWishartDensityConstant d (n + 1) = centralWishartDensityConstant d n *
      (Real.pi⁻¹) ^ n * ((Nat.factorial (d + n) : ℕ) : ℝ)⁻¹ := by
  simp only [centralWishartDensityConstant, Fin.prod_univ_castSucc, Fin.val_castSucc,
    Fin.val_last, mul_assoc]

def centralWishartCoordinateDensity (d n : ℕ) (q : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ := by
  classical
  exact if (hermitianOfRealCoordinates q).PosDef then ENNReal.ofReal
    (centralWishartDensityConstant d n * (hermitianOfRealCoordinates q).det.re ^ d *
      Real.exp (-(hermitianOfRealCoordinates q).trace.re)) else 0

theorem measurable_centralWishartCoordinateDensity (d n : ℕ) :
    Measurable (centralWishartCoordinateDensity d n) := by
  classical
  unfold centralWishartCoordinateDensity
  refine Measurable.ite ((measurableSet_complex_posDef n).preimage
    continuous_hermitianOfRealCoordinates.measurable) ?_ measurable_const
  have hH := continuous_hermitianOfRealCoordinates (n := n)
  apply ENNReal.measurable_ofReal.comp
  exact (show Continuous (fun q =>
    (centralWishartDensityConstant d n * (hermitianOfRealCoordinates q).det.re ^ d *
      Real.exp (-(hermitianOfRealCoordinates q).trace.re))) by fun_prop).measurable

theorem gammaPDF_nat_succ_positive (k : ℕ) (r : ℝ) (hr : 0 < r) :
    gammaPDF ((k + 1 : ℕ) : ℝ) 1 r = ENNReal.ofReal
      (((Nat.factorial k : ℕ) : ℝ)⁻¹ * r ^ k * Real.exp (-r)) := by
  rw [gammaPDF_of_nonneg hr.le]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial, Real.one_rpow,
    add_sub_cancel_right, Real.rpow_natCast, one_mul, one_div]

end
end JinWishart

#print axioms JinWishart.complexVectorGramRankOne_trace
#print axioms JinWishart.centralBartlettGram_trace
#print axioms JinWishart.centralBartlettGram_isHermitian
#print axioms JinWishart.centralBartlettGram_posDef_iff
#print axioms JinWishart.hermitianOfRealCoordinates_centralChart
#print axioms JinWishart.centralWishartDensityConstant_pos
#print axioms JinWishart.centralWishartDensityConstant_succ
#print axioms JinWishart.measurable_centralWishartCoordinateDensity
#print axioms JinWishart.gammaPDF_nat_succ_positive
