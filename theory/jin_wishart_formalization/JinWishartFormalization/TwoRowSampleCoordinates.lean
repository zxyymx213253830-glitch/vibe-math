import JinWishartFormalization.NoncentralFourDimensionalGaussianCDF
import JinWishartFormalization.NoncentralOneColumnEnergy

/-!
# Coordinates for the actual two-row complex sample

The four real coordinates of a `2 × 1` complex sample are identified with
`Fin 4`.  The chosen equivalence sends the real part of the first row to the
first coordinate, which lets an axial deterministic mean use the four-
dimensional Gaussian theorem directly.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

/-- Reindex the four real coordinates of a two-row, one-column sample so that
the real coordinate at matrix entry `(0,0)` is coordinate zero. -/
def twoRowSampleIndexEquiv : ((Fin 2 × Fin 1) × Fin 2) ≃ Fin 4 := by
  let e := Fintype.equivFinOfCardEq
    (show Fintype.card (((Fin 2 × Fin 1) × Fin 2)) = 4 by simp)
  exact e.trans (Equiv.swap (e ((0, 0), 0)) 0)

/-- The induced linear isometry from the actual sample space to four real
coordinates. -/
def twoRowSampleToFin4 :
    ComplexSample (m := 2) (n := 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ twoRowSampleIndexEquiv

theorem stdGaussian_map_twoRowSampleToFin4 :
    (stdGaussian (ComplexSample (m := 2) (n := 1))).map twoRowSampleToFin4 =
      stdGaussian (EuclideanSpace ℝ (Fin 4)) :=
  stdGaussian_map twoRowSampleToFin4

/-- A `2 × 1` mean supported on its first real component maps to the axial
four-dimensional mean. The `1/√2` compensates for the complex-sample encoding. -/
def twoRowAxialMean (a : ℝ) : Matrix (Fin 2) (Fin 1) ℂ :=
  fun i _ => if i = 0 then (a / Real.sqrt 2 : ℝ) else 0

private theorem twoRowAxialSampleMean_coord (a : ℝ)
    (i : (Fin 2 × Fin 1) × Fin 2) :
    complexSampleMean (twoRowAxialMean a) i =
      if i = ((0, 0), 0) then a else 0 := by
  rcases i with ⟨⟨i, j⟩, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [complexSampleMean, twoRowAxialMean] <;>
    (have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
     calc
       Real.sqrt 2 * (a / Real.sqrt 2) =
           a * (Real.sqrt 2 * (Real.sqrt 2)⁻¹) := by ring
       _ = a := by rw [mul_inv_cancel₀ hs, mul_one])

theorem twoRowSampleToFin4_complexSampleMean (a : ℝ) :
    twoRowSampleToFin4 (complexSampleMean (twoRowAxialMean a)) =
      a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ) := by
  ext k
  have hzero : twoRowSampleIndexEquiv.symm 0 = ((0, 0), 0) := by
    simp [twoRowSampleIndexEquiv]
  have hpre (k : Fin 4) :
      twoRowSampleIndexEquiv.symm k = ((0, 0), 0) ↔ k = 0 := by
    constructor
    · intro h
      have := congrArg twoRowSampleIndexEquiv h
      simpa [twoRowSampleIndexEquiv] using this
    · intro hk
      rw [hk, hzero]
  simp [twoRowSampleToFin4, LinearIsometryEquiv.piLpCongrLeft_apply,
    twoRowAxialSampleMean_coord, hpre, EuclideanSpace.single_apply]

/-- The real-coordinate mean encoding preserves the physical noncentrality
parameter: half its squared Euclidean norm is the one-column squared
Frobenius norm of the complex matrix mean. -/
theorem twoRowComplexMean_norm_sq_div_two
    (M : Matrix (Fin 2) (Fin 1) ℂ) :
    ‖complexSampleMean M‖ ^ 2 / 2 = ∑ i : Fin 2, ‖M i 0‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [complexSampleMean, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Complex.sq_norm, Complex.normSq_apply,
    Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The actual `2 × 1` sample-space shifted-ball probability with an axial mean
is exactly the standard four-dimensional Gaussian probability. -/
theorem twoRowAxialShiftedBall_eq_fourDBall (a R : ℝ) :
    (stdGaussian (ComplexSample (m := 2) (n := 1)))
        (Metric.closedBall (-complexSampleMean (twoRowAxialMean a)) R) =
      (stdGaussian (EuclideanSpace ℝ (Fin 4)))
        (Metric.closedBall
          (-(a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ))) R) := by
  rw [← stdGaussian_map_twoRowSampleToFin4]
  rw [Measure.map_apply (twoRowSampleToFin4.continuous.measurable)
    measurableSet_closedBall]
  have hball := twoRowSampleToFin4.preimage_closedBall
    (-(a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ))) R
  rw [hball]
  congr 1
  rw [← twoRowSampleToFin4_complexSampleMean]
  simp

/-- The actual two-row noncentral smallest-eigenvalue CDF, for a mean
concentrated in one real component, is the normalized Nuttall-Q formula. -/
theorem noncentralTwoRowAxialCDF_eq_one_sub_nuttallQ21
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := 2) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (twoRowAxialMean a) (by norm_num))) x =
      1 - (nuttallQ 2 1 a (Real.sqrt (2 * x)) / (a : ℂ)).re := by
  rw [cdf_eq_real, measureReal_def]
  rw [noncentralColumnSmallestEigenvalue_sublevelMass_eq_shiftedBall
    (m := 2) (by norm_num) (twoRowAxialMean a) x hx]
  rw [twoRowAxialShiftedBall_eq_fourDBall]
  rw [← measureReal_def]
  exact stdGaussian_fourDBall_axial_eq_one_sub_nuttallQ21 a
    (Real.sqrt (2 * x)) ha (Real.sqrt_nonneg _)

end

end JinWishart
