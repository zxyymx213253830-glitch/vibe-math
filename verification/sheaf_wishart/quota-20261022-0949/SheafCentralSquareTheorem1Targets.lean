import JinWishartFormalization.Theorem1CentralSquare
import Lean
open Matrix JinWishart Polynomial MeasureTheory ProbabilityTheory
namespace SheafCentralSquareTheorem1
noncomputable section
def OverlapTarget : Prop := ∀ (n : ℕ) (i j : Fin n),
  (∑ k : Fin n,i.val.choose k.val*j.val.choose k.val)=(i.val+j.val).choose j.val
def FactorTarget : Prop := ∀ n : ℕ,
  factorialHankel n=factorialPascalFactor n*(factorialPascalFactor n).transpose
def FactorDetTarget : Prop := ∀ n : ℕ,
  (factorialHankel n).det=∏ i : Fin n,(i.val.factorial : ℂ)^2
def MonicTarget : Prop := ∀ (n : ℕ) (F : ℂ[X] →ₗ[ℂ] ℂ)
  (p : Fin n → ℂ[X]) (hd : ∀ i,(p i).natDegree=i.val) (hm : ∀ i,(p i).Monic),
  Matrix.det (fun i j : Fin n => F (p i*p j))=
    Matrix.det (fun i j : Fin n => F (X^(i.val+j.val)))
def ShiftTarget : Prop := ∀ (n : ℕ) (F : ℂ[X] →ₗ[ℂ] ℂ) (x : ℂ),
  Matrix.det (fun i j : Fin n => F ((X+C x)^(i.val+j.val)))=
    Matrix.det (fun i j : Fin n => F (X^(i.val+j.val)))
def MomentTarget : Prop := ∀ k : ℕ,
  factorialMomentFunctional ((X : ℂ[X])^k)=(k.factorial : ℂ)
def GammaMomentTarget : Prop := ∀ (k : ℕ) (x : ℝ) (hx : 0≤x),
  upperGammaNat k x=(Real.exp (-x) : ℂ)*factorialMomentFunctional ((X+C (x : ℂ))^k)
def GammaDetTarget : Prop := ∀ (n : ℕ) (x : ℝ) (hx : 0≤x),
  Matrix.det (fun i j : Fin n => upperGammaNat (i.val+j.val) x)=
    (Real.exp (-(n : ℝ)*x) : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)^2)
def PsiDetTarget : Prop := ∀ (n : ℕ) (x : ℝ) (hx : 0≤x),
  (theorem1PsiMatrix n n 0 (le_refl n) (Nat.zero_le n)
    (fun j : Fin 0 => Fin.elim0 j) x).det=
    (Real.exp (-(n : ℝ)*x) : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)^2)
def CandidateTarget : Prop := ∀ (n : ℕ) (x : ℝ) (hx : 0≤x),
  theorem1CdfCandidate n n 0 (le_refl n) (Nat.zero_le n)
    (fun j : Fin 0 => Fin.elim0 j) x=1-Real.exp (-(n : ℝ)*x)
def ActualTarget : Prop := ∀ (n : ℕ) (hn : 0<n) (x : ℝ) (hx : 0≤x),
  theorem1CdfCandidate n n 0 (le_refl n) (Nat.zero_le n)
    (fun j : Fin 0 => Fin.elim0 j) x=
    ((stdGaussian (ComplexSample (m := n) (n := n)))
      {z | centralSquareSampleMinimum n hn z≤x}).toReal
end
end SheafCentralSquareTheorem1
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
   (`JinWishart.binomial_overlap_sum_fin,`SheafCentralSquareTheorem1.OverlapTarget),
   (`JinWishart.factorialHankel_gram_factorization,`SheafCentralSquareTheorem1.FactorTarget),
   (`JinWishart.factorialHankel_det,`SheafCentralSquareTheorem1.FactorDetTarget),
   (`JinWishart.monic_polynomial_moment_det,`SheafCentralSquareTheorem1.MonicTarget),
   (`JinWishart.shifted_polynomial_moment_det,`SheafCentralSquareTheorem1.ShiftTarget),
   (`JinWishart.factorialMoment_X_pow,`SheafCentralSquareTheorem1.MomentTarget),
   (`JinWishart.upperGammaNat_eq_factorialMoment,`SheafCentralSquareTheorem1.GammaMomentTarget),
   (`JinWishart.upperGammaHankel_det,`SheafCentralSquareTheorem1.GammaDetTarget),
   (`JinWishart.theorem1CentralSquare_PsiDet,`SheafCentralSquareTheorem1.PsiDetTarget),
   (`JinWishart.theorem1CentralSquare_candidate_eq_expCDF,`SheafCentralSquareTheorem1.CandidateTarget),
   (`JinWishart.theorem1CentralSquare_candidate_eq_actualCDF,`SheafCentralSquareTheorem1.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF central-square Theorem1 target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
