import JinWishartFormalization.ActualDiagonalGramMGF
import Lean
open Matrix MeasureTheory ProbabilityTheory Real JinWishart
universe u
namespace SheafDiagonalMGF
noncomputable section
def ProductIntegral : Prop := ∀ (ι : Type u) [Fintype ι] (a t : ι → ℝ),
 (∀ i,t i<1) → (∫ x : ι → ℝ,exp (∑ i,t i*(x i+a i)^2/2) ∂Measure.pi (fun _ : ι => gaussianReal 0 1))=
 (∏ i,(sqrt (1-t i))⁻¹)*exp (∑ i,(a i)^2*t i/(2*(1-t i)))
def ProductL1 : Prop := ∀ (ι : Type u) [Fintype ι] (a t : ι → ℝ),
 (∀ i,t i<1) → Integrable (fun x : ι → ℝ => exp (∑ i,t i*(x i+a i)^2/2)) (Measure.pi (fun _ : ι => gaussianReal 0 1))
def ActualIntegral : Prop := ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℝ),
 (∀ j,v j<1) → (∫ z : ComplexSample (m := m) (n := n),
 Real.exp (∑ j : Fin n,v j*(complexGram (complexSampleMatrix z+M) j j).re) ∂stdGaussian (ComplexSample (m := m) (n := n)))=
 (∏ a : Fin m × Fin n,(1-v a.2)⁻¹)*Real.exp (∑ a : Fin m × Fin n,‖M a.1 a.2‖^2*v a.2/(1-v a.2))
def ActualL1 : Prop := ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℝ),
 (∀ j,v j<1) → Integrable (fun z : ComplexSample (m := m) (n := n) =>
 Real.exp (∑ j : Fin n,v j*(complexGram (complexSampleMatrix z+M) j j).re)) (stdGaussian (ComplexSample (m := m) (n := n)))
end
end SheafDiagonalMGF
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.gaussianPi_integral_exp_weighted_shifted_squares,`SheafDiagonalMGF.ProductIntegral),
 (`JinWishart.gaussianPi_integrable_exp_weighted_shifted_squares,`SheafDiagonalMGF.ProductL1),
 (`JinWishart.actualNoncentralDiagonalGram_integral_exp,`SheafDiagonalMGF.ActualIntegral),
 (`JinWishart.actualNoncentralDiagonalGram_integrable_exp,`SheafDiagonalMGF.ActualL1)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Diagonal MGF literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
