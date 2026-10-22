import JinWishartFormalization.CanonicalBlockSpectrum

/-! Deterministic block shear identities. The solve condition N*K=H is
explicit; no inverse is silently totalized. No norm or probability claim. -/
open Matrix
namespace JinWishart
noncomputable section
variable {a b c : ℕ}

theorem canonical_block_shear_cancel (A : Matrix (Fin a) (Fin b) ℂ)
    (H K : Matrix (Fin c) (Fin b) ℂ) (N : Matrix (Fin c) (Fin c) ℂ)
    (hK : N * K = H) :
    fromBlocks A 0 H N * fromBlocks 1 0 (-K) 1 = fromBlocks A 0 0 N := by
  simp [fromBlocks_multiply, hK]

theorem canonical_block_shear_restore (A : Matrix (Fin a) (Fin b) ℂ)
    (H K : Matrix (Fin c) (Fin b) ℂ) (N : Matrix (Fin c) (Fin c) ℂ)
    (hK : N * K = H) :
    fromBlocks A 0 0 N * fromBlocks 1 0 K 1 = fromBlocks A 0 H N := by
  simp [fromBlocks_multiply, hK]

theorem canonical_block_shear_two_sided_inverse (K : Matrix (Fin c) (Fin b) ℂ) :
    fromBlocks 1 0 (-K) 1 * fromBlocks 1 0 K 1 = (1 : Matrix (Fin b ⊕ Fin c) (Fin b ⊕ Fin c) ℂ) ∧
    fromBlocks 1 0 K 1 * fromBlocks 1 0 (-K) 1 = (1 : Matrix (Fin b ⊕ Fin c) (Fin b ⊕ Fin c) ℂ) := by
  constructor <;> simp [fromBlocks_multiply, fromBlocks_one]

end
end JinWishart
#print axioms JinWishart.canonical_block_shear_cancel
#print axioms JinWishart.canonical_block_shear_restore
#print axioms JinWishart.canonical_block_shear_two_sided_inverse
