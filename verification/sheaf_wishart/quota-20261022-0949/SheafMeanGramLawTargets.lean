import JinWishartFormalization.ActualNoncentralMeanGramLaw
import Lean
open Matrix MeasureTheory ProbabilityTheory JinWishart
namespace SheafMeanGramLaw
noncomputable section

def EqualGram : Prop := ∀ {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℂ),
 Mᴴ * M = Nᴴ * N → complexNoncentralWishart M = complexNoncentralWishart N

def RightUnitary : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
 (U : Matrix (Fin n) (Fin n) ℂ), Uᴴ * U = 1 →
 (complexNoncentralWishart M).map (fun W => Uᴴ * W * U) = complexNoncentralWishart (M * U)

def Orbit : Prop := ∀ {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℂ)
 (U : Matrix (Fin n) (Fin n) ℂ), Uᴴ * U = 1 → Nᴴ * N = Uᴴ * (Mᴴ * M) * U →
 (complexNoncentralWishart M).map (fun W => Uᴴ * W * U) = complexNoncentralWishart N
end
end SheafMeanGramLaw
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.complexNoncentralWishart_eq_of_meanGram_eq,`SheafMeanGramLaw.EqualGram),
 (`JinWishart.complexNoncentralWishart_right_unitary_conjugation,`SheafMeanGramLaw.RightUnitary),
 (`JinWishart.complexNoncentralWishart_meanGram_unitary_transport,`SheafMeanGramLaw.Orbit)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Actual noncentral mean-Gram law literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
