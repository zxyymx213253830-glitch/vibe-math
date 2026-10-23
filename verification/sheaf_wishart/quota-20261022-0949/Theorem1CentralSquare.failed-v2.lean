import JinWishartFormalization.PolynomialMomentTranslation
import JinWishartFormalization.GammaFactorialMoment
import JinWishartFormalization.Theorem1Formula
import JinWishartFormalization.CentralWishartMinimum
import Mathlib.Data.Fin.Rev

/-! Original Theorem1 central square candidate equals the actual CN1 minimum
CDF in every positive size. Codex. Exact controls seed2026102246 precede source.
No assumed joint density, determinant sign hypothesis or normalization premise.
[需人工审查] Original paper indexing/model/variance and inherited probability law. -/
open Matrix MeasureTheory ProbabilityTheory Polynomial
namespace JinWishart
noncomputable section

theorem upperGammaHankel_det (n : ℕ) (x : ℝ) (hx : 0≤x) :
    Matrix.det (fun i j : Fin n => upperGammaNat (i.val+j.val) x)=
      (Real.exp (-(n : ℝ)*x) : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)^2) := by
  classical
  have heq : Matrix.of (fun i j : Fin n => upperGammaNat (i.val+j.val) x)=
      (Real.exp (-x) : ℂ) • Matrix.of (fun i j : Fin n =>
        factorialMomentFunctional ((X+C (x : ℂ))^(i.val+j.val))) := by
    ext i j
    exact upperGammaNat_eq_factorialMoment _ x hx
  change (Matrix.of (fun i j : Fin n => upperGammaNat (i.val+j.val) x)).det=_
  rw [heq,Matrix.det_smul,shifted_polynomial_moment_det]
  have h0 : (fun i j : Fin n => factorialMomentFunctional ((X : ℂ[X])^(i.val+j.val)))=
      factorialHankel n := by
    ext i j
    exact factorialMoment_X_pow _
  rw [h0,factorialHankel_det,Fintype.card_fin]
  have hp : (Real.exp (-x) : ℂ)^n=(Real.exp (-(n : ℝ)*x) : ℂ) := by
    rw [← Complex.ofReal_pow,← Real.exp_nat_mul]
    congr 2
    ring
  rw [hp]

theorem theorem1CentralSquare_PsiDet (n : ℕ) (x : ℝ) (hx : 0≤x) :
    (theorem1PsiMatrix n n 0 (le_refl n) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x).det=
      (Real.exp (-(n : ℝ)*x) : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)^2) := by
  have heq : theorem1PsiMatrix n n 0 (le_refl n) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x=
      Matrix.reindex (Fin.revPerm : Fin n ≃ Fin n) Fin.revPerm
        (Matrix.of (fun i j : Fin n => upperGammaNat (i.val+j.val) x)) := by
    ext i j
    simp only [theorem1PsiMatrix,theorem1PsiEntry,Nat.not_lt_zero,↓reduceDIte,
      Matrix.reindex_apply,Matrix.of_apply,Fin.revPerm_symm,Fin.revPerm_apply]
    congr 1
    simp only [theorem1GammaIndex,Fin.val_rev]
    omega
  rw [heq,Matrix.det_reindex_self,upperGammaHankel_det n x hx]

theorem theorem1CentralSquare_candidate_eq_expCDF (n : ℕ) (x : ℝ) (hx : 0≤x) :
    theorem1CdfCandidate n n 0 (le_refl n) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x=1-Real.exp (-(n : ℝ)*x) := by
  classical
  have hD : (∏ i : Fin n,(i.val.factorial : ℂ)^2)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero i.val)
  have hDN := norm_ne_zero_iff.mpr hD
  rw [theorem1CdfCandidate,theorem1CentralSquare_PsiDet n x hx,
    theorem1CentralSquare_PsiDet n 0 (by norm_num)]
  simp only [mul_zero,neg_zero,Real.exp_zero,Complex.ofReal_one,one_mul]
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_nonneg _),mul_div_cancel_right₀ _ hDN]

theorem theorem1CentralSquare_candidate_eq_actualCDF (n : ℕ) (hn : 0<n)
    (x : ℝ) (hx : 0≤x) :
    theorem1CdfCandidate n n 0 (le_refl n) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x=
      ((stdGaussian (ComplexSample (m := n) (n := n)))
        {z | centralSquareSampleMinimum n hn z≤x}).toReal := by
  rw [theorem1CentralSquare_candidate_eq_expCDF n x hx,
    actualCentralSquare_minimum_CDF n hn x hx]

end
end JinWishart
#print axioms JinWishart.upperGammaHankel_det
#print axioms JinWishart.theorem1CentralSquare_PsiDet
#print axioms JinWishart.theorem1CentralSquare_candidate_eq_expCDF
#print axioms JinWishart.theorem1CentralSquare_candidate_eq_actualCDF
