I'll review the four concrete issues you've identified in this P4 codex file.

## Review of Strictness, Zero Inverse/Nullset, Positivity Transfer, and Tail/CDF Signs

### 1. **Strictness** (`actualNoncentral_minimum_pos_ae`)

**Status: Correct.**
- The theorem proves `0 < complexNoncentralSampleSmallestEigenvalue` almost everywhere, not merely `≤`.
- Uses `complexSample_shiftedGram_posDef_ae` which gives positive-definiteness (strict), then extracts the eigenvalue at the minimum index.
- The `filter_upwards` + `eigenvalues_pos` chain correctly transfers strict positivity from the Gram matrix to its smallest eigenvalue.
- No issue: strict inequality is preserved throughout.

### 2. **Zero Inverse / Nullset** (`actualNoncentralInverseMinimumTail_eq`)

**Status: Correct handling via explicit null-set removal.**

Key observations:
- Lean defines `0⁻¹ = 0` by convention (`inv_zero`). Without the a.e. positivity result, the set `{z | r ≤ λ_min(z)⁻¹}` would include points where `λ_min = 0` (mapping to `r ≤ 0`, false for `r > 0`, but definitionally messy).
- The `filter_upwards [actualNoncentral_minimum_pos_ae ...]` explicitly removes the zero-eigenvalue locus before reasoning about reciprocals.
- Inside the filtered set, `hz : 0 < λ_min(z)` justifies `le_div_iff₀ hz` — division by strictly positive is safe.
- `measure_congr` then equates the two sets modulo a null set, so `.toReal` (which extracts the real measure) agrees.

**No issue:** The null set where `λ_min = 0` is explicitly quotiented out by `filter_upwards`. The reciprocal is well-defined on the support.

### 3. **Positivity Transfer** (from Gram → eigenvalue → reciprocal tail)

**Status: Correct chain.**

Transfer path:
```
shiftedGram_posDef_ae  →  eigenvalues_pos (all > 0)  →  smallestEigenvalue > 0  →  inverse exists & finite
```

- `smallestEigenvalue₀Index` picks a valid index (requires `hn : 0 < n`, satisfied by `Nat.succ_pos n`).
- `Fintype.equivOfCardEq` reindexes correctly; `simpa` handles the bookkeeping.
- For the tail: since `λ_min > 0` a.e., the map `z ↦ λ_min(z)⁻¹` is measurable and finite a.e., so the tail set `{z | r ≤ λ_min⁻¹}` is measurable.

**No issue:** Positivity transfers cleanly through each layer.

### 4. **Tail / CDF Signs and Direction** (`_eq`, `_log_exponent`, `_power_bounds`)

**Status: Correct. Non-strict inequality `r ≤ λ⁻¹` matches CDF at `λ ≤ r⁻¹`.**

Detailed sign check for `hr : 0 < r`:
- `r ≤ λ⁻¹` with `λ > 0` ⟺ `r · λ ≤ 1` ⟺ `λ ≤ r⁻¹` (using `le_div_iff₀` twice: once for `hz : 0 < λ`, once for `hr : 0 < r`).
- This is exactly `actualNoncentralMinimumCDF d n M r⁻¹` (the CDF evaluated at threshold `r⁻¹`).
- The `simp only [inv_eq_one_div, le_div_iff₀ hz, le_div_iff₀ hr, mul_comm]` correctly performs this bidirectional rewrite.

**Log exponent:**
- `Tendsto ... (-((d+1 : ℕ) : ℝ))` — the negative sign is correct because as `r → ∞`, `tail ~ c/r^{d+1}`, so `log(tail)/log(r) → -(d+1)`.
- Uses `congr'` with `eventually_gt_atTop 0` to ensure `hr : 0 < r` holds eventually, then rewrites via `_eq`.

**Power bounds for `r ≥ 4`:**
- `hr : 4 ≤ r` implies `r⁻¹ ≤ 1/4`, satisfying the small-threshold condition `hs` needed by `actualNoncentralMinimumCDF_local_power_bounds`.
- `simpa only [inv_pow, div_eq_mul_inv]` converts `(r⁻¹)^{d+1}` to `r^{-(d+1)}` correctly.
- Both lower and upper bounds transfer with matching signs.

**No issue:** All inequalities, directions, and sign conventions are consistent.

---

## Summary Verdict

| Issue | Status |
|-------|--------|
| Strictness of minimum eigenvalue | ✅ Strict positivity proved a.e. |
| Zero inverse / null-set handling | ✅ Explicitly removed via `filter_upwards`; `inv_zero = 0` never reached on support |
| Positivity transfer (Gram → eigen → tail) | ✅ Clean chain, all preconditions met |
| Tail/CDF equivalence and signs | ✅ `r ≤ λ⁻¹ ⟺ λ ≤ r⁻¹` for `r, λ > 0`; log exponent sign correct; power bounds direction correct |

**Overall: No concrete defects found.** The four `[需人工审查]` concerns are all handled correctly by the existing proofs. The file is sound as-is for P4 purposes.
