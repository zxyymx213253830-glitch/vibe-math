import JinWishartFormalization.WideRowInverseMoments
import Lean
open Matrix MeasureTheory ProbabilityTheory
namespace SheafWideRowInverse
noncomputable section
def Integrability : Prop := ∀ (m n : ℕ) (hm : 0<m) (_hmn : m≤n)
 (M : Matrix (Fin m) (Fin n) ℂ) (p : ℝ),0<p →
 (Integrable (fun X=>((JinWishart.gramSmallestValue Xᴴ hm)⁻¹)^p)
 (JinWishart.complexGaussianMatrixLaw M) ↔ p<((n-m+1 : ℕ) : ℝ))
def Divergence : Prop := ∀ (m n : ℕ) (hm : 0<m) (_hmn : m≤n)
 (M : Matrix (Fin m) (Fin n) ℂ) (p : ℝ),((n-m+1 : ℕ) : ℝ)≤p →
 (∫⁻ X,ENNReal.ofReal (((JinWishart.gramSmallestValue Xᴴ hm)⁻¹)^p)
 ∂JinWishart.complexGaussianMatrixLaw M)=⊤
end
end SheafWideRowInverse
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.wideRowMinimum_inverse_realMoment_integrable_iff,`SheafWideRowInverse.Integrability),
 (`JinWishart.wideRowMinimum_inverse_realMoment_lintegral_eq_top,`SheafWideRowInverse.Divergence)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
