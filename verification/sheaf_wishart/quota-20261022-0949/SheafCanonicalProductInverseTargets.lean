import JinWishartFormalization.CanonicalProductInverseCriterion
import Lean
open Matrix JinWishart MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace SheafCanonicalProductInverse
noncomputable section
def CriterionTarget : Prop := ∀ {a b c m n : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (MA : Matrix (Fin a) (Fin b) ℂ) (MH : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) (hN : IsUnit N.det)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (j : Fin (Fintype.card (Fin b))) (hj : j.val+1=min a b)
    (k : Fin (Fintype.card (Fin c))) (hk : k.val+1=c)
    (p : ℝ) (hp : 0<p),
    Integrable (fun w : ComplexSample (m := a) (n := b) × ComplexSample (m := c) (n := b) =>
      ((complexGram_posSemidef (canonicalFinBlock er ec (complexSampleMatrix w.1+MA)
        (complexSampleMatrix w.2+MH) N)).1.eigenvalues₀ i)⁻¹^p)
      ((stdGaussian (ComplexSample (m := a) (n := b))).prod
        (stdGaussian (ComplexSample (m := c) (n := b)))) ↔
      p<((max a b-min a b+1 : ℕ) : ℝ)
end
end SheafCanonicalProductInverse
open Lean Meta in
#eval show MetaM Unit from do
 let actualType ← inferType (← mkConstWithFreshMVarLevels `JinWishart.canonical_product_inverse_realMoment_integrable_iff)
 let expectedType ← whnf (← mkConstWithFreshMVarLevels `SheafCanonicalProductInverse.CriterionTarget)
 unless ← isDefEq actualType expectedType do
  throwError "SHEAF canonical product inverse criterion target differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
