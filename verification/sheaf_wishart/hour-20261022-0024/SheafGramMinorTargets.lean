import JinWishartFormalization.GramRankSpectralCoefficient
import JinWishartFormalization.RectangularDeterminantExpansion
import Lean
open Matrix Polynomial
namespace SheafGramMinor
noncomputable section
def Spectral : Prop := ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (c : ℂ),
 (1+c • A).det = ∏ i, (1+c*(hA.eigenvalues i : ℂ))
def Poly : Prop := ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian),
 (1+(Polynomial.X : ℂ[X]) • A.map Polynomial.C).det = ∏ i,(1+Polynomial.C (hA.eigenvalues i : ℂ)*Polynomial.X)
def Coeff : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ),
 ((1+(Polynomial.X : ℂ[X]) • (JinWishart.complexGram A).map Polynomial.C).det).coeff A.rank =
 ∏ i ∈ Finset.univ.filter (fun i => (JinWishart.complexGram_posSemidef A).1.eigenvalues i ≠ 0),
 ((JinWishart.complexGram_posSemidef A).1.eigenvalues i : ℂ)
def Pos : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ),
 0 < (((1+(Polynomial.X : ℂ[X]) • (JinWishart.complexGram A).map Polynomial.C).det).coeff A.rank).re
def Log : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ),
 Real.log (((1+(Polynomial.X : ℂ[X]) • (JinWishart.complexGram A).map Polynomial.C).det).coeff A.rank).re =
 ∑ i,if 0 < (JinWishart.complexGram_posSemidef A).1.eigenvalues i then Real.log ((JinWishart.complexGram_posSemidef A).1.eigenvalues i) else 0
def Expand : Prop := ∀ {q m : ℕ} (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ),
 (A*B).det = ∑ f : Fin q → Fin m,(∏ i,A i (f i))*(B.submatrix f id).det
def Zero : Prop := ∀ {q m : ℕ} (B : Matrix (Fin m) (Fin q) ℂ) (f : Fin q → Fin m),
 ¬Function.Injective f → (B.submatrix f id).det=0
def Row : Prop := ∀ {q m : ℕ} (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ),
 (A*B).det≠0 → ∃ f : Fin q → Fin m,Function.Injective f ∧ (B.submatrix f id).det≠0
def Compress : Prop := ∀ {m n q : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (L : Matrix (Fin q) (Fin m) ℂ)
 (H : Matrix (Fin n) (Fin q) ℂ), (L*X*H).det≠0 →
 ∃ (f : Fin q → Fin m) (g : Fin q → Fin n),Function.Injective f ∧ Function.Injective g ∧ (X.submatrix f g).det≠0
def Rank : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ),
 ∃ (f : Fin X.rank → Fin m) (g : Fin X.rank → Fin n),Function.Injective f ∧ Function.Injective g ∧ (X.submatrix f g).det≠0
end
end SheafGramMinor
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
  (`JinWishart.hermitian_det_one_add_complex_smul,`SheafGramMinor.Spectral),
  (`JinWishart.hermitian_det_polynomial_eq_product,`SheafGramMinor.Poly),
  (`JinWishart.gram_rank_coefficient_eq_nonzero_product,`SheafGramMinor.Coeff),
  (`JinWishart.gram_rank_coefficient_re_pos,`SheafGramMinor.Pos),
  (`JinWishart.gram_rank_coefficient_log_eq_positive_sum,`SheafGramMinor.Log),
  (`JinWishart.det_mul_rectangular_sum_functions,`SheafGramMinor.Expand),
  (`JinWishart.det_submatrix_eq_zero_of_not_injective,`SheafGramMinor.Zero),
  (`JinWishart.exists_injective_row_minor_of_mul_det_ne_zero,`SheafGramMinor.Row),
  (`JinWishart.exists_coordinate_minor_of_compression_det_ne_zero,`SheafGramMinor.Compress),
  (`JinWishart.exists_rank_coordinate_minor,`SheafGramMinor.Rank)] do
   let actualType ← inferType (← mkConstWithFreshMVarLevels target)
   let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
   unless ← isDefEq actualType expectedType do
    throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
