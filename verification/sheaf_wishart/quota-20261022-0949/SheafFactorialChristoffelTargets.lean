import JinWishartFormalization.FactorialLaguerreOrthogonality
import JinWishartFormalization.ChristoffelMomentDeterminant
import Lean
open Polynomial Matrix JinWishart
namespace SheafFactorialChristoffel
noncomputable section
def Alternating : Prop := ∀ (n j : ℕ), j<n →
 (∑ k ∈ Finset.range (n+1),(-1 : ℂ)^(n-k)*(n.choose k : ℂ)*((j+k).factorial : ℂ)/(k.factorial : ℂ))=0
def MonicTarget : Prop := ∀ (n : ℕ),(factorialLaguerre n).Monic
def DegreeTarget : Prop := ∀ (n : ℕ),(factorialLaguerre n).natDegree=n
def OrthogonalTarget : Prop := ∀ (n j : ℕ), j<n → factorialMomentFunctional ((X : ℂ[X])^j*factorialLaguerre n)=0
def EvalTarget : Prop := ∀ (n : ℕ) (x : ℂ),(-1 : ℂ)^n*(factorialLaguerre n).eval (-x)=
 (n.factorial : ℂ)*∑ k ∈ Finset.range (n+1),(n.choose k : ℂ)*x^k/(k.factorial : ℂ)
def ColumnsTarget : Prop := ∀ (n : ℕ) (G : Fin n → ℂ[X] →ₗ[ℂ] ℂ) (p : Fin n → ℂ[X]),
 (∀ i,(p i).natDegree=i.val) → (∀ i,(p i).Monic) →
 Matrix.det (fun i j : Fin n => G i (p j))=Matrix.det (fun i j : Fin n => G i (X^j.val))
def ChristoffelTarget : Prop := ∀ (n : ℕ) (F : ℂ[X] →ₗ[ℂ] ℂ) (p : ℂ[X]),
 p.natDegree=n → p.Monic → (∀ i : Fin n,F (X^i.val*p)=0) → ∀ (z : ℂ),
 Matrix.det (fun i j : Fin n => F ((X-C z)*X^(i.val+j.val)))=
 (-1 : ℂ)^n*p.eval z*Matrix.det (fun i j : Fin n => F (X^(i.val+j.val)))
end
end SheafFactorialChristoffel
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.factorial_alternating_moment_sum,`SheafFactorialChristoffel.Alternating),
  (`JinWishart.factorialLaguerre_monic,`SheafFactorialChristoffel.MonicTarget),
  (`JinWishart.factorialLaguerre_natDegree,`SheafFactorialChristoffel.DegreeTarget),
  (`JinWishart.factorialLaguerre_moment_orthogonal,`SheafFactorialChristoffel.OrthogonalTarget),
  (`JinWishart.factorialLaguerre_eval_neg,`SheafFactorialChristoffel.EvalTarget),
  (`JinWishart.monic_functional_columns_det,`SheafFactorialChristoffel.ColumnsTarget),
  (`JinWishart.christoffel_moment_det,`SheafFactorialChristoffel.ChristoffelTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF factorial Christoffel target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
