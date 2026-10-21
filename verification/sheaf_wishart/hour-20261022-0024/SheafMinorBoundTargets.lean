import JinWishartFormalization.GramMinorLogDomination
import Lean
open Matrix Polynomial
namespace SheafMinorBound
noncomputable section
def Weight : Prop := ∀ {q m : ℕ} (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ) (σ : Equiv.Perm (Fin q)),
 (∑ f : Fin q → Fin m,(∏ i,A (σ i) (f i))*(B.submatrix f id).det) = ((Equiv.Perm.sign σ : ℤ):ℂ)*(A*B).det
def Average : Prop := ∀ {q m : ℕ} (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ),
 (q.factorial:ℂ)*(A*B).det = ∑ f : Fin q → Fin m,(A.submatrix id f).det*(B.submatrix f id).det
def Squares : Prop := ∀ {m q : ℕ} (B : Matrix (Fin m) (Fin q) ℂ),
 (q.factorial:ℂ)*(JinWishart.complexGram B).det = ∑ f : Fin q → Fin m,star ((B.submatrix f id).det)*(B.submatrix f id).det
def Minor : Prop := ∀ {m q : ℕ} (B : Matrix (Fin m) (Fin q) ℂ) (f : Fin q → Fin m),
 Complex.normSq ((B.submatrix f id).det) ≤ (q.factorial:ℝ)*(JinWishart.complexGram B).det.re
def Select : Prop := ∀ {m n q : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (g : Fin q → Fin n), Function.Injective g →
 (JinWishart.complexGram (X.submatrix id g)).det.re ≤ (((1+(Polynomial.X:ℂ[X]) • (JinWishart.complexGram X).map Polynomial.C).det).coeff q).re
def Coeff : Prop := ∀ {m n q : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (f : Fin q → Fin m) (g : Fin q → Fin n), Function.Injective g →
 Complex.normSq ((X.submatrix f g).det) ≤ (q.factorial:ℝ)*(((1+(Polynomial.X:ℂ[X]) • (JinWishart.complexGram X).map Polynomial.C).det).coeff q).re
def Ordered : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ),
 Real.log (((1+(Polynomial.X:ℂ[X]) • (JinWishart.complexGram X).map Polynomial.C).det).coeff X.rank).re =
 ∑ i,JinWishart.positiveSpectrumLog ((JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i)
def Dom : Prop := ∀ {m n q : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (f : Fin q → Fin m) (g : Fin q → Fin n), Function.Injective g → X.rank=q → (X.submatrix f g).det≠0 →
 |∑ i,JinWishart.positiveSpectrumLog ((JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i)| ≤
 (∑ i,(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i)+|Real.log (q.factorial:ℝ)|+2*|Real.log ‖(X.submatrix f g).det‖|
end
end SheafMinorBound
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
  (`JinWishart.rectangular_det_permutation_weight_sum,`SheafMinorBound.Weight),
  (`JinWishart.det_mul_rectangular_factorial_sum_functions,`SheafMinorBound.Average),
  (`JinWishart.gram_det_factorial_sum_squared_minors,`SheafMinorBound.Squares),
  (`JinWishart.squared_minor_le_factorial_gram_det,`SheafMinorBound.Minor),
  (`JinWishart.selected_gram_det_le_coefficient,`SheafMinorBound.Select),
  (`JinWishart.squared_coordinate_minor_le_factorial_coefficient,`SheafMinorBound.Coeff),
  (`JinWishart.gram_rank_coefficient_log_eq_ordered_positive_sum,`SheafMinorBound.Ordered),
  (`JinWishart.abs_positive_log_sum_le_minor_log,`SheafMinorBound.Dom)] do
   let actualType ← inferType (← mkConstWithFreshMVarLevels target)
   let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
   unless ← isDefEq actualType expectedType do
    throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
