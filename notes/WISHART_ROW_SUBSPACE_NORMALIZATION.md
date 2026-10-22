# Fixed injective deterministic row block normalization

Codex proof: RowSubspaceNormalization.lean. For any injective complex linear
map L:E->F between finite dimensional complex inner product spaces, there
are a,r with r=dim E and a+r=dim F, a complex linear isometry equivalence
V:F->Euclidean(a+r), and a linear equivalence N:E->Euclidean(r), such that
V(Lx)=(0,Nx) in the explicit Sum-indexed coordinates. Empty E/F are included.
N need not be isometric. This is a noncomputable existence theorem.

The proof uses the orthogonal decomposition F=range L plus its orthogonal
complement and full orthonormal representations, then swaps the two factors.
It does not yet compose the B/M joint normal form or assert a Gaussian law,
block independence, or the general singular inverse-moment threshold.

Reuses the already recorded canonical_normal_form_control.py seed2026102222,
11 exact cases/55 checks, including row-unitary, zero upper-right mean block,
invertible remaining mean block, and empty-dimensional references. These
are the same controls reused at702, not55 new checks and not a general proof.
Final source and one literal expected type pass the shared Lean gate with
standard three axioms. No source changes after the full-source P4 snapshot.

## Different-family P4 and exact resolution

Real Qoder Qwen3.8-Max, tools disabled, final source fully supplied. The raw
response is retained and reports no mathematical gap in the decomposition.
Its three type/API concerns are resolved against the pinned sources:

1. Mathlib Analysis/InnerProductSpace/PiL2.lean defines OrthonormalBasis with
   a field repr : E equiv_linear_isometry EuclideanSpace, at lines393-395.
   stdOrthonormalBasis at1076 returns precisely that full basis. Subspaces
   inherit their own finite-dimensional inner product space structure; the
   expressions S and S-orthogonal are the subtype spaces, not support sets.
2. ba.repr has domain S-orthogonal, so its argument0 is typed as that subtype
   zero. The immediately preceding hd statement explicitly annotates this
   zero, and map_zero is applied to the actual representation map.
3. LinearEquiv.ofInjective in Algebra/Module/Submodule/Equiv.lean165 has only
   the injectivity hypothesis, no Nonempty/positive-dimension assumption.
   N.finrank_eq and V.finrank_eq prove the two dimension identities directly;
   their simp proofs include Fin0. No non-degeneracy step is omitted.

P4 is scoped model review, not human review or independent compilation.
[需人工审查] Subsequent coupled Gaussian law, Fubini/Holder/limits, physical
variance, and singular inverse-moment transport remain required. Frozen
papers/PDF/upload/code archives unchanged; full Lake/mathlib and independent
Linux kernel NOT_RUN.
