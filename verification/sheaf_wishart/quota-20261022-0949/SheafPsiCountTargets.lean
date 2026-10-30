import JinWishartFormalization.PsiCandidateCountPolynomial
import Lean
open MeasureTheory Matrix Set Polynomial Finset JinWishart
namespace SheafPsiCountTargets
noncomputable section
def psiCountPolynomial_transport : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (x : ℝ) (hx : 0 ≤ x),
 Polynomial.C (((Equiv.Perm.sign ((psiZeroColumnEquiv p L).symm.trans
   (psiZeroRowEquiv p L)) : ℤˣ) : ℂ)) * psiCountPolynomial p L q lambda x =
 Polynomial.C (((∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) : ℝ) : ℂ) *
   (mixedCandidateCountPolynomial p L q lambda x).map Complex.ofRealHom
def mixedCandidateCountPolynomial_restricted : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j) (x : ℝ) (hx : 0 ≤ x),
 mixedCandidateCountPolynomial p L q lambda x =
 (rowAffinePolynomialMatrix
   (Matrix.of (fun i j => ∫ y in Ioi x, mixedEnsembleF p L i y *
     mixedEnsembleG p L q lambda j y ∂(volume.restrict (Ioi (0 : ℝ)))))
   (Matrix.of (fun i j => ∫ y in Iic x, mixedEnsembleF p L i y *
     mixedEnsembleG p L q lambda j y ∂(volume.restrict (Ioi (0 : ℝ)))))).det
def mixedCandidateEnsemble_count_tail_polynomial : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x)
 (k : ℕ) (hk : k ≤ p+L),
 ((mixedCandidateEnsemble p L q lambda)
   {z | coordinateMembershipCount (Ioi x) z = k}).toReal =
 (mixedCandidateCountPolynomial p L q lambda x).coeff k /
   (mixedCandidateTailMatrix p L q lambda 0).det
def paperPsi_zero_det_signed_transport : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : ∀ j, 0 ≤ lambda j),
 (((Equiv.Perm.sign ((psiZeroColumnEquiv p L).symm.trans
   (psiZeroRowEquiv p L)) : ℤˣ) : ℂ)) *
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det =
 (((∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) : ℝ) : ℂ) *
   ((mixedCandidateTailMatrix p L q lambda 0).det : ℂ)
def mixedCandidateEnsemble_count_eq_psi_coefficient : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x)
 (k : ℕ) (hk : k ≤ p+L),
 (((mixedCandidateEnsemble p L q lambda)
   {z | coordinateMembershipCount (Ioi x) z = k}).toReal : ℂ) =
 (psiCountPolynomial p L q lambda x).coeff k /
   (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det
end
end SheafPsiCountTargets
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.psiCountPolynomial_transport,`SheafPsiCountTargets.psiCountPolynomial_transport),
 (`JinWishart.mixedCandidateCountPolynomial_restricted,`SheafPsiCountTargets.mixedCandidateCountPolynomial_restricted),
 (`JinWishart.mixedCandidateEnsemble_count_tail_polynomial,`SheafPsiCountTargets.mixedCandidateEnsemble_count_tail_polynomial),
 (`JinWishart.paperPsi_zero_det_signed_transport,`SheafPsiCountTargets.paperPsi_zero_det_signed_transport),
 (`JinWishart.mixedCandidateEnsemble_count_eq_psi_coefficient,`SheafPsiCountTargets.mixedCandidateEnsemble_count_eq_psi_coefficient)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Psi count target type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
