# P4 Adversarial Review

## ActualSingularPositiveLog.lean

**Mathematical gap: compression identity type mismatch.** `coordinate_submatrix_as_compression` states `(1 : Matrix (Fin m) (Fin m) ℂ).submatrix f (Equiv.refl _) * X * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Equiv.refl _) g = X.submatrix f g`. The LHS multiplies an `(m × m)` matrix by an `(m × n)` matrix by an `(n × n)` matrix, yielding `(m × n)`, but the RHS is `(q × q)`. This is a genuine dimensional inconsistency unless `q = m = n`, which is not assumed. The subsequent use in `exists_actual_fixed_rank_minor_log_witness` to rewrite `L * X * H = X.submatrix f g` inherits this error. This is a **blocking mathematical gap**, not an API question—the stated equality cannot hold as written for general `q`.

**Mathematical gap: witness rank depends on Z₀, but claim is existential over fixed B,M.** `exists_actual_fixed_rank_minor_log_witness` obtains `Z₀` from `exists_matrix_affine_comp_maximal_rank`, then extracts witnesses `f, g` from `Z₀ * B + M`. The integrability and AE-nonvanishing conclusions are correct for that specific choice, but the theorem statement implies the witnesses work for the affine family `z ↦ z * B + M` generically. The logical structure is sound (existential introduction), but the witness depends on the rank-maximizing point `Z₀`, not merely on `B, M` algebraically. This is not a gap per se, but the `[需人工审查]` flag correctly identifies that the "fixed witness" is fixed *after* choosing `Z₀`, which could mislead downstream interpretation.

**Potential gap: `sampleEval_ne_zero_ae` application.** The proof applies `sampleEval_ne_zero_ae hp (0 : Matrix (Fin m) (Fin p) ℂ)` where `hp : genericAffineCompressedDet B M L H ≠ 0`. This requires that evaluating the polynomial at the mean of the zero matrix suffices. Since `complexSampleMean 0 = 0`, the shift is trivial, and the nonvanishing of the generic polynomial implies AE nonvanishing under the Gaussian measure. This step is logically valid assuming `sampleEval_ne_zero_ae` is correctly stated in dependencies. No gap here, but worth noting the zero-matrix choice is not arbitrary—it exploits linearity of the mean.

**No gap: integrability bootstrapping.** The `integrable_actualCorrelated_positive_log_sum` proof correctly uses `mono'` with domination by the trace plus log-determinant terms. The `filter_upwards` combines AE rank equality and AE minor nonvanishing. Standard measure-theoretic reasoning; no issue.

## GramMinorLogDomination.lean

**No mathematical gaps identified.** The domination bound `abs_positive_log_sum_le_minor_log` is deterministic algebra given the explicit premises `hr : X.rank = q` and `hp : (X.submatrix f g).det ≠ 0`. The coefficient bound `squared_coordinate_minor_le_factorial_coefficient` is imported as a dependency. The logarithmic inequality manipulation via `Real.log_le_log_iff` correctly handles positivity conditions. The eigenvalue reindexing through `Fintype.equivOfCardEq` is standard.

## Summary

One **actual blocking mathematical gap**: the compression identity in `coordinate_submatrix_as_compression` has a dimensional type error for general `q ≠ m` or `q ≠ n`. This propagates into the main witness theorem. Everything else is logically coherent given stated dependencies.
