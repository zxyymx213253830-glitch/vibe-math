import JinWishartFormalization.RectangularWishartOneExtraRow
import JinWishartFormalization.Theorem1Formula

/-!
# Unmodified Theorem 1 candidate: central three rows and two columns

Codex proof bodies. Actual CDF is supplied by the dimension-general one-extra-row
cone-polynomial theorem; no new specialized Bartlett/chart construction.
[需人工审查] Original paper (s,t,L)=(2,3,0), variance and eigenvalue convention.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem theorem1CentralTwoColumnThreeRows_PsiMatrix (x : ℝ) (hx : 0 ≤ x) :
    theorem1PsiMatrix 2 3 0 (by omega) (by omega)
        (fun j : Fin 0 => Fin.elim0 j) x =
      (!![(Real.exp (-x) : ℂ) * ((x : ℂ)^3 + 3*(x : ℂ)^2 + 6*(x : ℂ) + 6),
          (Real.exp (-x) : ℂ) * ((x : ℂ)^2 + 2*(x : ℂ) + 2);
          (Real.exp (-x) : ℂ) * ((x : ℂ)^2 + 2*(x : ℂ) + 2),
          (Real.exp (-x) : ℂ) * ((x : ℂ) + 1)] : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [theorem1PsiMatrix, theorem1PsiEntry, theorem1GammaIndex,
      upperGammaNat_eq_finite _ hx, upperGammaNatFinite, Finset.sum_range_succ] <;> ring

theorem theorem1CentralTwoColumnThreeRows_PsiDet (x : ℝ) (hx : 0 ≤ x) :
    (theorem1PsiMatrix 2 3 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x).det =
      (Real.exp (-2*x) : ℂ) * ((x : ℂ)^2 + 4*(x : ℂ) + 2) := by
  rw [theorem1CentralTwoColumnThreeRows_PsiMatrix x hx, Matrix.det_fin_two]
  have he : (Real.exp (-x) : ℂ)^2 = (Real.exp (-2*x) : ℂ) := by
    have her : Real.exp (-x)^2 = Real.exp (-2*x) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    exact_mod_cast her
  calc
    _ = (Real.exp (-x) : ℂ)^2 * ((x : ℂ)^2 + 4*(x : ℂ) + 2) := by simp; ring
    _ = _ := by rw [he]

theorem theorem1CentralTwoColumnThreeRows_candidate_eq_polynomial (x : ℝ) (hx : 0 ≤ x) :
    theorem1CdfCandidate 2 3 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x =
        1 - Real.exp (-2*x) * oneExtraRowMinimumPolynomial 2 x := by
  have hp : 0 ≤ x^2 + 4*x + 2 := by positivity
  have he : ((x : ℂ)^2 + 4*(x : ℂ) + 2) = ((x^2 + 4*x + 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [theorem1CdfCandidate, theorem1CentralTwoColumnThreeRows_PsiDet x hx,
    theorem1CentralTwoColumnThreeRows_PsiDet 0 (by norm_num), he,
    norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _), Complex.norm_of_nonneg hp]
  norm_num [oneExtraRowMinimumPolynomial, Finset.sum_range_succ]
  ring

/-- Original candidate, unchanged, equals the true actual central 3-by-2 CDF. -/
theorem theorem1CentralTwoColumnThreeRows_candidate_eq_actualCDF (x : ℝ) (hx : 0 ≤ x) :
    theorem1CdfCandidate 2 3 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x =
      ((stdGaussian (ComplexSample (m := 3) (n := 2)))
        {z | oneExtraRowSampleMinimum 2 (by norm_num) z ≤ x}).toReal := by
  rw [theorem1CentralTwoColumnThreeRows_candidate_eq_polynomial x hx,
    actualOneExtraRow_minimum_CDF 2 (by norm_num) x hx]
  norm_num

end
end JinWishart

#print axioms JinWishart.theorem1CentralTwoColumnThreeRows_PsiMatrix
#print axioms JinWishart.theorem1CentralTwoColumnThreeRows_PsiDet
#print axioms JinWishart.theorem1CentralTwoColumnThreeRows_candidate_eq_polynomial
#print axioms JinWishart.theorem1CentralTwoColumnThreeRows_candidate_eq_actualCDF
