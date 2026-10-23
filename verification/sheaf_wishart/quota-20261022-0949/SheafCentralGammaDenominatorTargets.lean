import JinWishartFormalization.CentralGammaDenominator
import Lean
open Matrix JinWishart
namespace SheafCentralGammaDenominator
noncomputable section
def OffsetTarget : Prop := ∀ n d : ℕ,
  Matrix.det (fun i j : Fin n => ((d+i.val+j.val).factorial : ℂ))=
    ∏ i : Fin n,(i.val.factorial : ℂ)*((d+i.val).factorial : ℂ)
def ZeroTarget : Prop := ∀ (s t : ℕ) (hst : s≤t),
  (theorem1PsiMatrix s t 0 hst (Nat.zero_le s)
    (fun j : Fin 0 => Fin.elim0 j) 0).det=
    ∏ i : Fin s,(i.val.factorial : ℂ)*((t-s+i.val).factorial : ℂ)
def PositiveTarget : Prop := ∀ (s t : ℕ) (hst : s≤t),
  0<‖(theorem1PsiMatrix s t 0 hst (Nat.zero_le s)
    (fun j : Fin 0 => Fin.elim0 j) 0).det‖
end
end SheafCentralGammaDenominator
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
   (`JinWishart.factorialHankel_offset_det,`SheafCentralGammaDenominator.OffsetTarget),
   (`JinWishart.theorem1Central_PsiDet_zero,`SheafCentralGammaDenominator.ZeroTarget),
   (`JinWishart.theorem1Central_PsiDet_zero_norm_pos,`SheafCentralGammaDenominator.PositiveTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF central Gamma denominator target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
