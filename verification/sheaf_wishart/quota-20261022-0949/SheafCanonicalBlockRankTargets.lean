import JinWishartFormalization.CanonicalBlockRank
import Lean
open Matrix JinWishart
namespace SheafCanonicalBlockRank
noncomputable section
def RankTarget : Prop := ∀ {a b c m n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) (hN : IsUnit N.det),
    (canonicalFinBlock er ec A H N).rank=A.rank+c
end
end SheafCanonicalBlockRank
open Lean Meta in
#eval show MetaM Unit from do
 let actualType ← inferType (← mkConstWithFreshMVarLevels `JinWishart.canonical_fin_block_rank)
 let expectedType ← whnf (← mkConstWithFreshMVarLevels `SheafCanonicalBlockRank.RankTarget)
 unless ← isDefEq actualType expectedType do
  throwError "SHEAF canonical block rank target differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
