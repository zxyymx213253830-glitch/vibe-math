# Canonical block rank with an invertible fixed block

For arbitrary rectangular A and H, square N with IsUnit N.det, and arbitrary compatible Fin row/column equivalences, canonical_fin_block_rank proves rank(reindex [[A,0],[H,N]])=rank A+c. A may be zero or rank deficient; no Gaussian/full-small-side-rank premise is used. Empty dimensions are included. This supplies the rank input needed to apply the accepted canonical positive-minimum comparison on actual Gaussian blocks.

The private kernel equivalence identifies ker diag(A,N) with ker A by projection to the first coordinates and extension by zero. Injectivity of N kills the second kernel coordinates. Rank-nullity gives the diagonal rank, then K=N inverse*H and the already proved two-sided shear inverse transfer the rank to [[A,0],[H,N]]. Final Fin reindexing preserves rank.

Seed2026102234:64 exact cases/193 checks, deliberately rank-one/zero A, invertible triangular N, empty dimensions, and a singular-N negative control. These controls are not a general proof. Final v2 and one literal target type pass the shared serial Lean gate with standard three axioms. Source v1 composition-normalization failures remain archived and unaccepted.

## Qoder P4 resolution

The real final-source Qwen3.8-Max response finds no actual mathematical gaps. The definition of canonicalFinBlock is exactly Fin reindexing of fromBlocks A 0 H N, with no further transformation. The imported shear cancel equation is exactly D*Sminus=diag(A,N) under N*K=H; its two-sided inverse yields the determinant unit for the right multiplier. Matrix.mul_nonsing_inv accepts the supplied IsUnit N.det, and rank_mul_eq_left_of_isUnit_det preserves the left factor's rank under right multiplication by its invertible square argument. These are pinned, hash-bound, kernel-checked dependencies. In zero-row A cases the kernel equivalence is ker diag(A,N)~the full first-coordinate space, not ker N alone; rank-nullity includes zero dimensions.

Scoped P4 is not human review/independent compilation. [需人工审查] Subsequent physical-model/AE/product-integration assembly. General singular B inverse threshold remains OPEN; frozen publication artifacts unchanged; full Lake/mathlib and Linux independent kernel NOT_RUN.
