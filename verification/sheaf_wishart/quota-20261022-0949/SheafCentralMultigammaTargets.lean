import JinWishartFormalization.CentralMultigammaBridge
import Lean
open Matrix JinWishart
namespace SheafCentralMultigamma
noncomputable section
def DeterminantTarget : Prop := ∀ (s t : ℕ) (hst : s≤t),
  (theorem1PsiMatrix s t 0 hst (Nat.zero_le s)
    (fun j : Fin 0 => Fin.elim0 j) 0).det=
    ((T3NormalizationAudit.factorialMultigamma s s*
      T3NormalizationAudit.factorialMultigamma s t : ℝ) : ℂ)
def DisplayedTarget : Prop := ∀ (s t : ℕ) (hst : s≤t),
  T3NormalizationAudit.paperC3 s t 0 (fun j : Fin 0 => Fin.elim0 j)*
    (theorem1PsiMatrix s t 0 hst (Nat.zero_le s)
      (fun j : Fin 0 => Fin.elim0 j) 0).det.re=
    T3NormalizationAudit.factorialMultigamma s t
def DerivedTarget : Prop := ∀ (s t : ℕ) (hst : s≤t),
  (T3NormalizationAudit.paperC3 s t 0 (fun j : Fin 0 => Fin.elim0 j)/
    T3NormalizationAudit.factorialMultigamma s t)*
    (theorem1PsiMatrix s t 0 hst (Nat.zero_le s)
      (fun j : Fin 0 => Fin.elim0 j) 0).det.re=1
end
end SheafCentralMultigamma
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
   (`JinWishart.theorem1Central_PsiDet_zero_eq_multigamma,`SheafCentralMultigamma.DeterminantTarget),
   (`JinWishart.centralDisplayedC3_times_PsiDet_zero,`SheafCentralMultigamma.DisplayedTarget),
   (`JinWishart.centralDerivedC3_times_PsiDet_zero,`SheafCentralMultigamma.DerivedTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF central multigamma target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
