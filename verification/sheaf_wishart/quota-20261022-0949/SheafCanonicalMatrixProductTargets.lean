import JinWishartFormalization.CanonicalMatrixProductInverse
import Lean
open Matrix JinWishart MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace SheafCanonicalMatrixProduct
noncomputable section
def CriterionTarget : Prop := ∀ {a b c m n : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (MA : Matrix (Fin a) (Fin b) ℂ) (MH : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) (hN : IsUnit N.det)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (j : Fin (Fintype.card (Fin b))) (hj : j.val+1=min a b)
    (k : Fin (Fintype.card (Fin c))) (hk : k.val+1=c) (p : ℝ) (hp : 0<p),
    Integrable (fun w : Matrix (Fin a) (Fin b) ℂ × Matrix (Fin c) (Fin b) ℂ =>
      ((complexGram_posSemidef (canonicalFinBlock er ec w.1 w.2 N)).1.eigenvalues₀ i)⁻¹^p)
      ((complexGaussianMatrixLaw MA).prod (complexGaussianMatrixLaw MH)) ↔
      p<((max a b-min a b+1 : ℕ) : ℝ)
def DivergenceTarget : Prop := ∀ {a b c m n : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (MA : Matrix (Fin a) (Fin b) ℂ) (MH : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) (hN : IsUnit N.det)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (j : Fin (Fintype.card (Fin b))) (hj : j.val+1=min a b)
    (k : Fin (Fintype.card (Fin c))) (hk : k.val+1=c)
    (p : ℝ) (hp : ((max a b-min a b+1 : ℕ) : ℝ)≤p),
    (∫⁻ w : Matrix (Fin a) (Fin b) ℂ × Matrix (Fin c) (Fin b) ℂ,
      ENNReal.ofReal (((complexGram_posSemidef (canonicalFinBlock er ec w.1 w.2 N)).1.eigenvalues₀ i)⁻¹^p)
      ∂(complexGaussianMatrixLaw MA).prod (complexGaussianMatrixLaw MH))=⊤
end
end SheafCanonicalMatrixProduct
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.canonical_matrix_product_inverse_realMoment_integrable_iff,`SheafCanonicalMatrixProduct.CriterionTarget),
 (`JinWishart.canonical_matrix_product_inverse_realMoment_lintegral_eq_top,`SheafCanonicalMatrixProduct.DivergenceTarget) ] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF canonical matrix product target differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
