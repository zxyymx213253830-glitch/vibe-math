## P4 Adversarial Review

### 1. ActualSingularPositiveLog.lean

**`coordinate_submatrix_as_compression`**: No issues. Pure matrix identity.

**`exists_actual_fixed_rank_minor_log_witness`**:
- **Math gap (minor)**: The proof selects a *specific* maximal-rank witness `Z₀` then extracts coordinate minor witnesses `f, g` from the deterministic matrix `Z₀*B + M`. It then asserts AE nonvanishing via `sampleEval_ne_zero_ae` applied to the polynomial `genericAffineCompressedDet B M L H`, which is shown nonzero by evaluating at `Z₀`. This is logically sound—no gap.
- **API question (not a math gap)**: Depends on `exists_matrix_affine_comp_maximal_rank`, `exists_rank_coordinate_minor`, `integrable_actualAffineCompressedDet_log`, and `sampleEval_ne_zero_ae`. These are external but their usage is type-consistent; no logical issue visible at this layer.

**`integrable_actualCorrelated_positive_log_sum`**:
- **Actual math gap**: The domination step uses `abs_positive_log_sum_le_minor_log` with the bound `(∑ i, actualCorrelatedEigenvalue ...) + |log r!| + 2*|log ‖det‖|`. Integrability of the RHS is constructed as `ht.add(...).add(hlog.norm.const_mul 2)`. However, `hlog` is integrability of `log ‖det‖`, so `hlog.norm` gives integrability of `‖log ‖det‖‖ = |log ‖det‖|`. The factor of 2 is handled by `const_mul`. **This is correct**—no gap.
- **Subtle point**: `actualCorrelatedRank_eq_generic_ae B M` is used to replace the random rank with the fixed `r` almost everywhere. This is essential and correctly applied in the `filter_upwards` block. No gap.

**`integrable_actualCorrelated_positive_log`**:
- **No gap**: Correctly delegates to `integrable_positiveSpectrumLog_of_sum`, passing the sum integrability just proved plus pointwise nonnegativity and individual eigenvalue integrability/measurability. Type signatures align.

**`actualCorrelatedMatrixLogDet_offset_generic_rank`**:
- **No gap**: Direct application of `actualCorrelatedMatrixLogDet_offset_of_sum_log` with the integrability condition just established. The offset coefficient is exactly `min m (fromRows B M).rank`, matching the claimed "expected generic-rank offset."

---

### 2. GramMinorLogDomination.lean

**`gram_rank_coefficient_log_eq_ordered_positive_sum`**:
- **No gap**: Reindexes unordered `eigenvalues` to ordered `eigenvalues₀` via `Fintype.equivOfCardEq`. Sum reindexing is valid. Relies on `gram_rank_coefficient_log_eq_positive_sum` (external, deterministic dependency).

**`abs_positive_log_sum_le_minor_log`**:
- **Potential math concern (resolved)**: The inequality `positiveSpectrumLog x ≤ x` for `x ≥ 0` is used in `hu`. Since `positiveSpectrumLog x = max 0 (log x)` or similar truncation, we have `positiveSpectrumLog x ≤ x` only when `x ≥ 1` gives `log x ≤ x`, and `0 < x < 1` gives `positiveSpectrumLog x = 0 ≤ x`. **This holds** assuming `positiveSpectrumLog` is defined as `max 0 (Real.log x)` or equivalent. Check that `positiveSpectrumLog_le_self` encodes this correctly (external, but standard).
- **No other gaps**: The squared-minor bound `hb`, positivity of factorial/coefficient/normSq, and log monotonicity are all correctly chained. The absolute-value triangle decomposition at the end (`linarith` with `neg_le_abs` / `le_abs_self`) is valid.

---

### Summary

**Actual mathematical gaps found: None.**

All proof bodies are internally consistent given their declared dependencies. The witness construction is deterministic-for-fixed-parameters, AE statements are correctly filtered, domination bounds match integrability constructions, and the offset limit is properly reduced. External API dependencies (`exists_matrix_affine_comp_maximal_rank`, `positiveSpectrumLog_le_self`, etc.) are used with correct types and cannot be verified as gaps without inspecting their definitions—but nothing in these files contradicts their expected contracts.
