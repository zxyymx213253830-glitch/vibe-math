## P4 Adversarial Review: `CanonicalFinGramTransport.lean`

**1. Critical: Index Type Mismatch in `canonicalFiniteGramCoordinate`**
The coordinate is defined over `Fin (Fintype.card (Fin n))`, which is `Fin n`. However, the proof of `canonical_fin_positive_coordinate_bounds` passes this index to bounds theorems expecting `Fin n` only after reindexing through `hi : i.val + 1 = min m n`. When `min m n < n` (the row-rank branch), the eigenvalue array has length `n` but only `m` positive eigenvalues exist. The condition `hi` forces `i.val = m - 1`, selecting the maximum index, but the definition doesn't enforce that `i` actually indexes into the nonzero spectrum—it's a coincidence of the proof's `hi` assumption, not a structural guarantee.

**2. Gap: `eigenvalueCongr` Triviality Masks Sorting Dependency**
The lemma states that if `A = B` then their sorted eigenvalue arrays are equal. This is just `congrArg`. However, the usage equates `(X*F)ᴴ*(X*F)` computed via `canonicalSumRowAction_gram` with `complexGram_posSemidef (X*F).1`. These are definitionally the same matrix, so the lemma adds nothing—but the *real* dependency is that `eigenvalues₀` uses a fixed sorting convention. If `complexGram_posSemidef` constructs its Hermitian proof differently (even for the same matrix), the `subst` works, but this is fragile to API refactoring. Not a mathematical gap, but a maintenance risk disguised as a theorem.

**3. Problem: `matrixColumnControl` Applied Without Semantic Justification**
The bound uses `max (matrixColumnControl F) (matrixColumnControl Fᴴ)` as a multiplicative factor on eigenvalues. This implicitly treats `matrixColumnControl` as an operator norm bound or spectral radius proxy. But no assumption connects `matrixColumnControl` to the spectral behavior of `F` as a linear map—it's applied to both `F` and `Fᴴ` symmetrically. If `matrixColumnControl` measures column-wise ℓ₂ norms (as the name suggests), then using `max` of it and its adjoint as a two-sided eigenvalue multiplier conflates column geometry with singular value bounds. The inequality direction `≤ max(...) * λᵢ(XᴴX)` requires that this max controls the largest singular value squared; this is a nontrivial claim imported from the dependency without verification here.

**4. Minor: Unused Positivity Hypotheses**
`hm : 0 < m` and `hn : 0 < n` are assumed but only `hn` is used in the column-rank branch and `hm` in the row-rank branch. Neither is needed for the Gram preservation or determinant unit claims. They're artifacts forwarded to dependencies.

**5. Determinant Unit Proof: Roundabout but Valid**
`canonical_reindexed_column_det_isUnit` proves injectivity of the square submatrix's linear map to conclude unit determinant. The chain `mulVec_injective_iff_isUnit` → `isUnit_iff_isUnit_det` is logically sound for square matrices over fields. No gap, though the intermediate `hxy'` step applying `WithLp.toLp 2` to both sides of a vector equality is redundant—`toEuclideanLin` already operates on `EuclideanSpace`.
