import JinWishartFormalization.OriginalPsiNormalizerProduct
import Lean
open Matrix Finset JinWishart
namespace SheafOriginalPsiNormProduct
noncomputable section
def Transport : Prop := ∀ (p L t : ℕ) (hst : p+L ≤ t) (lambda : Fin L → ℝ),
 (psiZeroRealMatrix (p+L) t L lambda).submatrix (psiZeroRowEquiv p L) (psiZeroColumnEquiv p L) =
   Matrix.of (fun i j => psiZeroColumnScale p L t lambda j *
     mixedNoncentralMomentMatrix (t-(p+L)) p L lambda i j)
def Formula : Prop := ∀ (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖ =
   (∏ j : Fin L, Real.rpow (lambda j) (((t-s : ℕ) : ℝ)/2))*
     ((∏ j : Fin L, lambda j^(s-L))*(∏ i : Fin L, ∏ j ∈ Ioi i, |lambda j-lambda i|))*
       (∏ h : Fin (s-L), (h.val.factorial : ℝ)*((t-s+h.val).factorial : ℝ))
end
end SheafOriginalPsiNormProduct
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.psiZeroRealMatrix_transport,`SheafOriginalPsiNormProduct.Transport),
 (`JinWishart.theorem1PsiMatrix_zero_norm_det_formula,`SheafOriginalPsiNormProduct.Formula)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Original Psi norm product literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
