import JinWishartFormalization.ActualNoncentralMatrixLaplace
import Lean
open Matrix MeasureTheory ProbabilityTheory Real Finset JinWishart
open scoped ComplexOrder
namespace SheafMatrixLaplace
noncomputable section
def MeanLaw : Prop := ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
 Uᴴ*U=1 → (complexGaussianMatrixLaw M).map (fun A => A*U)=complexGaussianMatrixLaw (M*U)
def Spectral : Prop := ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.PosSemidef),
 (∫ z : ComplexSample (m := m) (n := n),Real.exp (-(T*complexGram (complexSampleMatrix z+M)).trace.re) ∂stdGaussian (ComplexSample (m := m) (n := n)))=
 (∏ a : Fin m × Fin n,(1+hT.1.eigenvalues a.2)⁻¹)*Real.exp (-(∑ a : Fin m × Fin n,
 ‖(M*(hT.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) a.1 a.2‖^2*hT.1.eigenvalues a.2/(1+hT.1.eigenvalues a.2)))
def L1 : Prop := ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ),
 T.PosSemidef → Integrable (fun z : ComplexSample (m := m) (n := n) => Real.exp (-(T*complexGram (complexSampleMatrix z+M)).trace.re)) (stdGaussian (ComplexSample (m := m) (n := n)))
def Invariant : Prop := ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ),
 T.PosSemidef → (∫ z : ComplexSample (m := m) (n := n),Real.exp (-(T*complexGram (complexSampleMatrix z+M)).trace.re) ∂stdGaussian (ComplexSample (m := m) (n := n)))=
 (‖(1+T).det‖^m)⁻¹*Real.exp (-(M*T*(1+T)⁻¹*Mᴴ).trace.re)
def Law : Prop := ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ),
 T.PosSemidef → (∫ W : Matrix (Fin n) (Fin n) ℂ,Real.exp (-(T*W).trace.re) ∂complexNoncentralWishart M)=
 (‖(1+T).det‖^m)⁻¹*Real.exp (-(M*T*(1+T)⁻¹*Mᴴ).trace.re)
end
end SheafMatrixLaplace
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.complexGaussianMatrixLaw_right_unitary_mean,`SheafMatrixLaplace.MeanLaw),
 (`JinWishart.actualNoncentralPSD_integral_exp_spectral,`SheafMatrixLaplace.Spectral),
 (`JinWishart.actualNoncentralPSD_integrable_exp,`SheafMatrixLaplace.L1),
 (`JinWishart.actualNoncentralPSD_matrixLaplace,`SheafMatrixLaplace.Invariant),
 (`JinWishart.noncentralWishart_PSD_matrixLaplace,`SheafMatrixLaplace.Law)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Actual noncentral matrix Laplace literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
