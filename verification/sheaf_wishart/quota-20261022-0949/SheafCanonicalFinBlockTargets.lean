import JinWishartFormalization.CanonicalFinBlockComparison
import Lean
open Matrix JinWishart
open scoped ComplexOrder
namespace SheafCanonicalFinBlock
noncomputable section
def ShearTarget : Prop := ∀ {m n b c : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ) (hm : 0<m) (hn : 0<n)
    (hr : D.rank=min m n) (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n),
    let E := D*canonicalFinShear e (-K)
    let L := (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2
    0<(complexGram_posSemidef D).1.eigenvalues₀ i ∧
    0<(complexGram_posSemidef E).1.eigenvalues₀ i ∧
    (complexGram_posSemidef E).1.eigenvalues₀ i ≤ L*(complexGram_posSemidef D).1.eigenvalues₀ i ∧
    (complexGram_posSemidef D).1.eigenvalues₀ i ≤ L*(complexGram_posSemidef E).1.eigenvalues₀ i
def CharpolyTarget : Prop := ∀ {a b c m n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (A : Matrix (Fin a) (Fin b) ℂ) (N : Matrix (Fin c) (Fin c) ℂ),
    ((canonicalFinBlock er ec A 0 N)ᴴ*canonicalFinBlock er ec A 0 N).charpoly=
      (Aᴴ*A).charpoly*(Nᴴ*N).charpoly
def MinimumTarget : Prop := ∀ {a b c m n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (A : Matrix (Fin a) (Fin b) ℂ) (H K : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) (hK : N*K=H)
    (hm : 0<m) (hn : 0<n) (hr : (canonicalFinBlock er ec A H N).rank=min m n)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (j : Fin (Fintype.card (Fin b))) (k : Fin (Fintype.card (Fin c)))
    (hj : 0<(complexGram_posSemidef A).1.eigenvalues₀ j)
    (hk : 0<(complexGram_posSemidef N).1.eigenvalues₀ k)
    (hminA : ∀ l,0<(complexGram_posSemidef A).1.eigenvalues₀ l →
      (complexGram_posSemidef A).1.eigenvalues₀ j≤(complexGram_posSemidef A).1.eigenvalues₀ l)
    (hminN : ∀ l,0<(complexGram_posSemidef N).1.eigenvalues₀ l →
      (complexGram_posSemidef N).1.eigenvalues₀ k≤(complexGram_posSemidef N).1.eigenvalues₀ l),
    let D := canonicalFinBlock er ec A H N
    let q := min ((complexGram_posSemidef A).1.eigenvalues₀ j)
      ((complexGram_posSemidef N).1.eigenvalues₀ k)
    let L := (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2
    0<(complexGram_posSemidef D).1.eigenvalues₀ i ∧ 0<q ∧
    q≤L*(complexGram_posSemidef D).1.eigenvalues₀ i ∧
    (complexGram_posSemidef D).1.eigenvalues₀ i≤L*q
end
end SheafCanonicalFinBlock
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.canonical_fin_shear_positive_bounds,`SheafCanonicalFinBlock.ShearTarget),
 (`JinWishart.canonical_fin_diagonal_gram_charpoly,`SheafCanonicalFinBlock.CharpolyTarget),
 (`JinWishart.canonical_fin_block_minimum_bounds,`SheafCanonicalFinBlock.MinimumTarget) ] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF canonical Fin block target differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
