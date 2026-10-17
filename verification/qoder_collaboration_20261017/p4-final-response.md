## P4 Review: `GaussianGramDimensions.lean`

**Scope**: I am a strict independent reviewer from a different model family than the Codex proof author. I report only concrete issues found in the supplied source, scoped to the three files provided. I do not rewrite proofs. I acknowledge the follow-up correction: `n ≤ m` is indeed a consequence of `hA`, and positivity constraints are intentional domain restrictions for the probability interface.

### Concrete Issues Found

After careful re-examination incorporating the follow-up clarifications, **no concrete issues remain** in the supplied source. Specifically:

1. **`if_pos hA` fix**: The corrected simplification in `totalGramColumnSpaceReal_finrank` properly resolves the `ite_eq_left` failure. This is correct.

2. **Dimension bound `n ≤ m`**: Correctly derived within `totalGramColumnSpaceReal_orthogonal_finrank` via `finrank_add_finrank_orthogonal`, nonnegativity of dimension, and `omega`—not assumed externally. No issue.

3. **Positivity hypotheses `hn : 0 < n` and `hnm : n < m`**: These appear *only* in `stdGaussian_gram_column_energy_law` (the probability interface), where they are mathematically necessary for Gamma shape parameters to be well-defined. The pure linear-algebra theorems (`gramColumnMap_leftInverse`, `gramColumnSpace_finrank_complex/real`, `totalGramColumnSpaceReal_finrank`, `totalGramColumnSpaceReal_orthogonal_finrank`) correctly omit these assumptions. This is a deliberate and correct domain separation, not a bug.

4. **Edge cases under `hA : IsUnit (Aᴴ * A).det`**:
   - **`n = 0`**: Excluded by `hn` in the probability theorem; the algebraic theorems hold vacuously or reduce correctly (empty matrices, rank 0).
   - **`n = m`**: Permitted by `hA`. The orthogonal complement has real dimension `2*(m - m) = 0`. This is handled correctly by `totalGramColumnSpaceReal_orthogonal_finrank` without requiring `n < m` at the algebraic level.
   - **`n > m`**: Impossible under `hA`, since `IsUnit (Aᴴ * A).det` implies the `n × n` Gram matrix is invertible, forcing `rank(A) = n ≤ m`. No explicit hypothesis is needed; this is a mathematical consequence correctly left implicit.

5. **Real/complex rank doubling**: `gramColumnSpace_finrank_real` correctly applies `finrank_real_of_complex` to obtain `2 * n`. The orthogonal complement calculation in `totalGramColumnSpaceReal_orthogonal_finrank` uses `finrank_real_of_complex` on the ambient space `EuclideanSpace ℂ (Fin m)` to get `2 * m`, then subtracts `2 * n` via `omega`. This is consistent and correct.

6. **Singular patched-zero space**: `totalGramColumnSpaceReal` returns `⊥` on the singular locus. `totalGramColumnSpaceReal_projection` handles both branches via `by_cases hA`, using `Matrix.nonsing_inv_apply_not_isUnit` to show the projector vanishes on the singular set. Measurability is global. No issue.

7. **Half-real-norm variance convention**: `gaussianSplitEnergy` divides squared norms by 2, matching the `gammaMeasure k 1` / `gammaMeasure l 1` target (shape = complex dimension, scale = 1). The comment in `GaussianRandomSubspaceLaw.lean` explicitly documents this convention. Consistent across all three files.

8. **Measurability, Fubini, independence**: All required measurability premises (`measurable_totalGramColumnSpaceReal_projection`) are explicitly discharged. The skew-product/Fubini step in `stdGaussian_random_split_energy_law` is inherited from the supporting interface and applied correctly with explicit hypotheses. Independence in `indep_stdGaussian_random_split_energy_law` is an explicit premise (`hXY`), not silently inferred.

9. **Open problems**: The header correctly states Gaussian a.e. full rank and general Wishart density are OPEN. No false claims are made.

### Conclusion

**No concrete issues found in the supplied source**, scoped to the three files and incorporating the follow-up corrections. All identified potential concerns (edge cases, dimension bounds, positivity domains, rank doubling, singular handling, variance conventions, measurability) are either correctly handled or explicitly documented as open.

This review does not replace human review.
