import JinWishartFormalization.PsiActivePermutation
import Lean
open MeasureTheory Matrix Set Polynomial Finset JinWishart
namespace SheafPsiActiveTargets
noncomputable section
def psiActiveColumnPermutation_inl : Prop := ∀ (p L : ℕ) (π : Equiv.Perm (Fin L)) (a : Fin p),
 psiActiveColumnPermutation p L π (psiZeroColumnEquiv p L (Sum.inl a)) =
 psiZeroColumnEquiv p L (Sum.inl a)
def psiActiveColumnPermutation_inr : Prop := ∀ (p L : ℕ) (π : Equiv.Perm (Fin L)) (a : Fin L),
 psiActiveColumnPermutation p L π (psiZeroColumnEquiv p L (Sum.inr a)) =
 psiZeroColumnEquiv p L (Sum.inr (π a))
def psiMatrix_permute_active_columns : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) (x : ℝ),
 theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) (lambda ∘ π) x =
 (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).submatrix id
   (psiActiveColumnPermutation p L π)
def xiMatrix_permute_active_columns : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) (x : ℝ),
 theorem2XiMatrix (p+L) (p+L+q) L (by omega) (by omega) (lambda ∘ π) x =
 (theorem2XiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).submatrix id
   (psiActiveColumnPermutation p L π)
def psiCountPolynomial_permute_active : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) (x : ℝ),
 psiCountPolynomial p L q (lambda ∘ π) x =
 Polynomial.C (((Equiv.Perm.sign (psiActiveColumnPermutation p L π).symm : ℤˣ) : ℂ)) *
   psiCountPolynomial p L q lambda x
def psiZeroDet_permute_active : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)),
 (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) (lambda ∘ π) 0).det =
 (((Equiv.Perm.sign (psiActiveColumnPermutation p L π).symm : ℤˣ) : ℂ)) *
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det
def psiCountRatio_permute_active : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (π : Equiv.Perm (Fin L)) (x : ℝ) (k : ℕ),
 (psiCountPolynomial p L q (lambda ∘ π) x).coeff k /
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) (lambda ∘ π) 0).det =
 (psiCountPolynomial p L q lambda x).coeff k /
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det
def candidateCount_eq_paperThetaDetSum : Prop := ∀ (p L q : ℕ)
 (spectrum : OrderedPositiveNoncentralSpectrum L) (x : ℝ) (hx : 0 ≤ x)
 (k : ℕ) (hk : k ≤ p+L),
 (((mixedCandidateEnsemble p L q (spectrum.values ∘ Fin.revPerm))
   {z | coordinateMembershipCount (Ioi x) z = k}).toReal : ℂ) =
 theorem3ThetaDetSum (p+L) (p+L+q) L (k+1) (by omega) (by omega) spectrum x /
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) spectrum.values 0).det
end
end SheafPsiActiveTargets
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.psiActiveColumnPermutation_inl,`SheafPsiActiveTargets.psiActiveColumnPermutation_inl),
 (`JinWishart.psiActiveColumnPermutation_inr,`SheafPsiActiveTargets.psiActiveColumnPermutation_inr),
 (`JinWishart.psiMatrix_permute_active_columns,`SheafPsiActiveTargets.psiMatrix_permute_active_columns),
 (`JinWishart.xiMatrix_permute_active_columns,`SheafPsiActiveTargets.xiMatrix_permute_active_columns),
 (`JinWishart.psiCountPolynomial_permute_active,`SheafPsiActiveTargets.psiCountPolynomial_permute_active),
 (`JinWishart.psiZeroDet_permute_active,`SheafPsiActiveTargets.psiZeroDet_permute_active),
 (`JinWishart.psiCountRatio_permute_active,`SheafPsiActiveTargets.psiCountRatio_permute_active),
 (`JinWishart.candidateCount_eq_paperThetaDetSum,`SheafPsiActiveTargets.candidateCount_eq_paperThetaDetSum)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Psi active target type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
