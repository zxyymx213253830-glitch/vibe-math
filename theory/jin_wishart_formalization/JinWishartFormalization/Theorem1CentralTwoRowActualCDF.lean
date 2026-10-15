import JinWishartFormalization.TwoRowMinimumLaw
import JinWishartFormalization.Theorem1Formula
import JinWishartFormalization.DeepSeekMinimumCDF20261013.DeterminantFactor

/-!
# Theorem 1 candidate equals the actual CDF in the central complex 2x2 case

Codex composes the original formula candidate with the actual minimum law.
The determinant polynomial factor is locally authored under GUIDED_COLLABORATION.
The original candidate and all normalizing constants remain unchanged.
[需人工审查] Paper parameter mapping and unit complex variance conventions.
-/

open Matrix MeasureTheory ProbabilityTheory

namespace JinWishart
noncomputable section

theorem theorem1CentralTwoRow_PsiMatrix (x : ℝ) (hx : 0 ≤ x) :
    theorem1PsiMatrix 2 2 0 (by omega) (by omega)
        (fun j : Fin 0 => Fin.elim0 j) x =
      (!![(Real.exp (-x) : ℂ) * ((x : ℂ) ^ 2 + 2 * (x : ℂ) + 2),
          (Real.exp (-x) : ℂ) * ((x : ℂ) + 1);
          (Real.exp (-x) : ℂ) * ((x : ℂ) + 1), (Real.exp (-x) : ℂ)] :
        Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [theorem1PsiMatrix, theorem1PsiEntry, theorem1GammaIndex,
      upperGammaNat_eq_finite _ hx, upperGammaNatFinite, Finset.sum_range_succ] <;> ring

theorem theorem1CentralTwoRow_PsiDet (x : ℝ) (hx : 0 ≤ x) :
    (theorem1PsiMatrix 2 2 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x).det = (Real.exp (-2 * x) : ℂ) := by
  rw [theorem1CentralTwoRow_PsiMatrix x hx, deepseek_minimum_DeterminantFactor]
  have he : Real.exp (-x) ^ 2 = Real.exp (-2 * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  exact_mod_cast he

theorem theorem1CentralTwoRow_PsiDet_norm_zero :
    ‖(theorem1PsiMatrix 2 2 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) 0).det‖ = 1 := by
  rw [theorem1CentralTwoRow_PsiDet 0 (by norm_num)]
  norm_num

theorem theorem1CentralTwoRow_candidate_eq_expCDF (x : ℝ) (hx : 0 ≤ x) :
    theorem1CdfCandidate 2 2 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x = 1 - Real.exp (-2 * x) := by
  rw [theorem1CdfCandidate, theorem1CentralTwoRow_PsiDet x hx,
    theorem1CentralTwoRow_PsiDet_norm_zero,
    Complex.norm_of_nonneg (Real.exp_nonneg _), div_one]

/-- Original Theorem 1 determinant candidate equals the actual central complex
2x2 sample CDF. No density premise or changed normalization is introduced. -/
theorem theorem1CentralTwoRow_candidate_eq_actualCDF (x : ℝ) (hx : 0 ≤ x) :
    theorem1CdfCandidate 2 2 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) x =
      ((stdGaussian (ComplexSample (m := 2) (n := 2)))
        {z | twoRowActualMinimum z ≤ x}).toReal := by
  rw [theorem1CentralTwoRow_candidate_eq_expCDF x hx, actualTwoRow_minimum_CDF x hx]

end
end JinWishart

#print axioms JinWishart.theorem1CentralTwoRow_PsiMatrix
#print axioms JinWishart.theorem1CentralTwoRow_PsiDet
#print axioms JinWishart.theorem1CentralTwoRow_PsiDet_norm_zero
#print axioms JinWishart.theorem1CentralTwoRow_candidate_eq_expCDF
#print axioms JinWishart.theorem1CentralTwoRow_candidate_eq_actualCDF
