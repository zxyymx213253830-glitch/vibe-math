import JinWishartFormalization.TwoSurplusLaguerreSquares
import Lean
open Finset MeasureTheory ProbabilityTheory JinWishart
namespace SheafTwoSurplusSquares
noncomputable section
def Superset : Prop := ∀ (n : ℕ) (U : Finset (Fin n)),
 (∑ R : Finset (Fin n),if U⊆R then 1/(((n+1 : ℕ) : ℝ)*(n.choose R.card : ℝ)) else 0)=1/((U.card+1 : ℕ) : ℝ)
def Squares : Prop := ∀ (n : ℕ) (f : Finset (Fin n) → ℝ),
 (∑ U : Finset (Fin n),∑ V : Finset (Fin n),f U*f V/(((U ∪ V).card+1 : ℕ) : ℝ)) =
 ∑ R : Finset (Fin n),(∑ U ∈ R.powerset,f U)^2/(((n+1 : ℕ) : ℝ)*(n.choose R.card : ℝ))
def Polynomial : Prop := ∀ (n : ℕ) (x : ℝ),twoExtraRowMinimumPolynomial n x=
 (∑ k ∈ range (n+1),(oneExtraRowMinimumPolynomial k x)^2)/((n+1 : ℕ) : ℝ)
def CDF : Prop := ∀ (n : ℕ) (hn : 0<n) (x : ℝ),0≤x →
 ((stdGaussian (ComplexSample (m := n+2) (n := n))) {z | centralGaussianSampleMinimum (n+2) n hn z≤x}).toReal =
 1-Real.exp (-(n : ℝ)*x)*((∑ k ∈ range (n+1),(oneExtraRowMinimumPolynomial k x)^2)/((n+1 : ℕ) : ℝ))
end
end SheafTwoSurplusSquares
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.finiteSupersetKernel_sum,`SheafTwoSurplusSquares.Superset),
 (`JinWishart.finiteSubsetPairKernel_square_sum,`SheafTwoSurplusSquares.Squares),
 (`JinWishart.twoExtraRowMinimumPolynomial_eq_meanSquares,`SheafTwoSurplusSquares.Polynomial),
 (`JinWishart.actualTwoExtraRows_minimum_CDF_meanSquares,`SheafTwoSurplusSquares.CDF)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Finite subset square literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
