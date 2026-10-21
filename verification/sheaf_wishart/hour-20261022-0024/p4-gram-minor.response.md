# P4 Adversarial Review

## GramRankSpectralCoefficient.lean

**1. Missing positivity hypothesis in `hermitian_det_one_add_complex_smul` (Mathematical Gap)**

The theorem statement holds for arbitrary `c : ℂ`, but the proof uses `hA.eigenvalues` which requires `A` to be Hermitian (given) and the spectral decomposition `A = U * D * U*`. The identity `(1 + c • A).det = ∏ i, (1 + c * λᵢ)` is mathematically correct for all `c` when `A` is Hermitian. No gap here upon reflection—the eigenvalues are real, `c` is arbitrary complex, and both sides are well-defined. **Withdrawn as a gap.**

**2. `Polynomial.coeff_prod_of_natDegree_le` API dependency (Potential API Question)**

In `gram_rank_coefficient_eq_nonzero_product`, the final `simpa` invokes `Polynomial.coeff_prod_of_natDegree_le S p 1 hd`. This lemma must extract the top-degree coefficient of a product of degree-≤1 polynomials as the product of leading coefficients over exactly `S.card` factors. If this Mathlib lemma requires `natDegree p i = 1` uniformly rather than `≤ 1`, the proof fails because some factors in `S` could still have degree 0 if an eigenvalue is zero—but `S` filters out zeros, so each `p i` for `i ∈ S` has the form `1 + cᵢX` with `cᵢ ≠ 0`, giving `natDegree = 1`. **Not a gap**, but depends on the exact statement of `coeff_prod_of_natDegree_le` handling the `≤ 1` bound correctly when extracting `coeff S.card`.

**3. `Real.log_prod` requires nonzero terms (Mathematical Gap — Minor)**

In `gram_rank_coefficient_log_eq_positive_sum`, the rewrite `rw [Real.log_prod ...]` uses the hypothesis `(fun i hi => (Finset.mem_filter.mp hi).2)` which extracts `eigenvalues i ≠ 0`. However, `Real.log_prod` requires strictly **positive** terms, not merely nonzero. The filter only guarantees `≠ 0`, while positivity comes from `eigenvalues_nonneg` combined with `≠ 0`. The proof does combine these later in the `sum_congr` block, but the `log_prod` rewrite happens **before** establishing positivity. If `Real.log_prod` demands a proof of `0 < f i` rather than `f i ≠ 0`, this is a gap at the point of application.

**4. Empty matrix edge case in `gram_rank_coefficient_re_pos` (No Gap)**

When `A.rank = 0`, the product over an empty filter yields 1, and `0 < 1.re` holds. Correctly handled.

## RectangularDeterminantExpansion.lean

**5. `det_mul_rectangular_sum_functions` sum over all functions vs. injective functions (No Gap)**

The expansion sums over all `f : Fin q → Fin m`, including non-injective ones. The subsequent theorem `det_submatrix_eq_zero_of_not_injective` shows non-injective terms contribute zero determinants. This is logically consistent—not a Cauchy-Binet claim, just the raw multilinear expansion.

**6. `matrix_rank_compression` output dimensions (API Question, Not Mathematical Gap)**

`exists_rank_coordinate_minor` destructures `matrix_rank_compression X` into `L : Matrix (Fin q) (Fin m)` and `H : Matrix (Fin n) (Fin q)` where `q = X.rank`. The existence and properties are assumed as a checked dependency. No logical issue within this file.

**7. Transpose maneuvering in `exists_coordinate_minor_of_compression_det_ne_zero` (No Gap)**

The double application of `exists_injective_row_minor_of_mul_det_ne_zero`—first to `L*(X*H)`, then to `H^T * (X_f)^T`—correctly extracts injective witnesses `f` and `g`. The submatrix transpose identity at the end is definitionally sound.

## Summary

| # | File | Type | Severity |
|---|------|------|----------|
| 3 | GramRankSpectralCoefficient | Mathematical gap | Minor — `Real.log_prod` applied before positivity established in proof order |
| 2 | GramRankSpectralCoefficient | API question | Low — depends on exact `coeff_prod_of_natDegree_le` statement for `≤ 1` vs `= 1` |

All other constructions are logically coherent finite-dimensional linear algebra. No probability claims appear. Zero shapes and empty products are handled.
