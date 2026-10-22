import JinWishartFormalization.CanonicalBlockShear
import Lean
open Matrix
namespace SheafCanonicalBlock
noncomputable section
abbrev h {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) := isHermitian_conjTranspose_mul_self A

def Gram : Prop := ∀ {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
 (N : Matrix (Fin c) (Fin d) ℂ),
 (fromBlocks A 0 0 N)ᴴ * fromBlocks A 0 0 N = fromBlocks (Aᴴ*A) 0 0 (Nᴴ*N)
def Poly : Prop := ∀ {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
 (N : Matrix (Fin c) (Fin d) ℂ),
 ((fromBlocks A 0 0 N)ᴴ * fromBlocks A 0 0 N).charpoly = (Aᴴ*A).charpoly*(Nᴴ*N).charpoly
def Roots : Prop := ∀ {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
 (N : Matrix (Fin c) (Fin d) ℂ),
 ((fromBlocks A 0 0 N)ᴴ * fromBlocks A 0 0 N).charpoly.roots =
 (Aᴴ*A).charpoly.roots+(Nᴴ*N).charpoly.roots
def Members : Prop := ∀ {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
 (N : Matrix (Fin c) (Fin d) ℂ) (x : ℝ),
 ((∃ i, (h (fromBlocks A 0 0 N)).eigenvalues₀ i=x) ↔
 (∃ j, (h A).eigenvalues₀ j=x) ∨ (∃ k, (h N).eigenvalues₀ k=x))
def Minimum : Prop := ∀ {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
 (N : Matrix (Fin c) (Fin d) ℂ)
 (i : Fin (Fintype.card (Fin b ⊕ Fin d)))
 (j : Fin (Fintype.card (Fin b))) (k : Fin (Fintype.card (Fin d))),
 0<(h (fromBlocks A 0 0 N)).eigenvalues₀ i → 0<(h A).eigenvalues₀ j → 0<(h N).eigenvalues₀ k →
 (∀ l,0<(h (fromBlocks A 0 0 N)).eigenvalues₀ l →
 (h (fromBlocks A 0 0 N)).eigenvalues₀ i≤(h (fromBlocks A 0 0 N)).eigenvalues₀ l) →
 (∀ l,0<(h A).eigenvalues₀ l → (h A).eigenvalues₀ j≤(h A).eigenvalues₀ l) →
 (∀ l,0<(h N).eigenvalues₀ l → (h N).eigenvalues₀ k≤(h N).eigenvalues₀ l) →
 (h (fromBlocks A 0 0 N)).eigenvalues₀ i=min ((h A).eigenvalues₀ j) ((h N).eigenvalues₀ k)
def Cancel : Prop := ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
 (H K : Matrix (Fin c) (Fin b) ℂ) (N : Matrix (Fin c) (Fin c) ℂ),
 N*K=H → fromBlocks A 0 H N * fromBlocks 1 0 (-K) 1=fromBlocks A 0 0 N
def Restore : Prop := ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
 (H K : Matrix (Fin c) (Fin b) ℂ) (N : Matrix (Fin c) (Fin c) ℂ),
 N*K=H → fromBlocks A 0 0 N * fromBlocks 1 0 K 1=fromBlocks A 0 H N
def Inverse : Prop := ∀ {b c : ℕ} (K : Matrix (Fin c) (Fin b) ℂ),
 fromBlocks 1 0 (-K) 1 * fromBlocks 1 0 K 1=(1 : Matrix (Fin b ⊕ Fin c) (Fin b ⊕ Fin c) ℂ) ∧
 fromBlocks 1 0 K 1 * fromBlocks 1 0 (-K) 1=(1 : Matrix (Fin b ⊕ Fin c) (Fin b ⊕ Fin c) ℂ)
end
end SheafCanonicalBlock
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.canonical_block_gram,`SheafCanonicalBlock.Gram),
 (`JinWishart.canonical_block_gram_charpoly,`SheafCanonicalBlock.Poly),
 (`JinWishart.canonical_block_gram_roots,`SheafCanonicalBlock.Roots),
 (`JinWishart.canonical_block_eigenvalue_mem_iff,`SheafCanonicalBlock.Members),
 (`JinWishart.canonical_block_min_positive,`SheafCanonicalBlock.Minimum),
 (`JinWishart.canonical_block_shear_cancel,`SheafCanonicalBlock.Cancel),
 (`JinWishart.canonical_block_shear_restore,`SheafCanonicalBlock.Restore),
 (`JinWishart.canonical_block_shear_two_sided_inverse,`SheafCanonicalBlock.Inverse)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
