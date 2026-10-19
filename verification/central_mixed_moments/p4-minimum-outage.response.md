# P4 Review: Worst-Mode Outage Corollary

## 1. Monotone Event Sign (Critical)

**`minimum_mode_log_threshold` is correct.** For `r > 0`, the map `l ↦ log(1 + r·l)` is strictly increasing on `[0, ∞)`, so the equivalence preserves direction. The hypothesis `hl : 0 ≤ l` is present but **unused in the proof term** (`nlinarith` doesn't need it because `log_le_iff_le_exp` and `le_div_iff₀ hr` handle the algebra). This is fine — `hl` documents the physical domain and matches the eigenvalue nonnegativity fact used downstream. No issue.

## 2. NonnegGram Scope (Correct Wiring)

**`actualNoncentralMinimumModeOutage_eq_CDF` is correct.** The call `complexNoncentralGram_eigenvalues₀_nonneg _ _ _` supplies exactly the `hl` needed by `minimum_mode_log_threshold`. The `congr 1; ext z` reduces set-equality to pointwise equivalence, and the threshold lemma does the rest. The `hr : 0 < r` hypothesis is correctly threaded. No issue.

## 3. Units / Physical Scope (Documentation Gap — P4)

The comment block says "Rate R is measured in natural-log units" but **no Lean type or hypothesis enforces `R > 0`** at the definition level. The outage definition `actualNoncentralMinimumModeOutage` accepts any `R : ℝ`. This is mathematically harmless (the CDF is defined for all real thresholds), but physically, a negative rate in natural units would mean `exp(R) - 1 < 0`, making the threshold `(exp(R)-1)/r` negative, which conflicts with `l ≥ 0`. The set `{z | ...}` would then be empty and the probability trivially 0.

**Recommendation:** Add a doc-level remark (not a hypothesis) noting that `R > 0` is the physical regime of interest, matching the `hR : 0 < R` in the diversity theorem. This is P4-only — no code change required, just awareness.

## 4. Diversity Exponent (Correct)

**`actualNoncentralMinimumModeOutage_diversity` is correct.** The key step:
- `hb : 0 < Real.exp R - 1` from `hR : 0 < R` via `one_lt_exp_iff` ✓
- Threshold `t := (exp R - 1)` is a fixed positive constant independent of `r` ✓
- `.congr'` with `eventually_gt_atTop 0` ensures `hr : 0 < r` for the `_eq_CDF` rewrite ✓
- The high-SNR exponent from `actualNoncentralCovarianceMinimumCDF_highSNR_diversity` applies directly since `t > 0` is constant ✓

The exponent `-((d+1 : ℕ) : ℝ)` is the covariance diversity order, correctly inherited. No sharp constant or G2 claim is made. ✓

## 5. Application Scope (P4 Confirmed)

This is explicitly a **minor monotone-transform corollary**: applying a strictly increasing function to the minimum eigenvalue and translating the threshold. No new probabilistic content beyond the already-checked generic CDF/high-SNR results. Correctly scoped.

---

## Verdict

**All three theorems are sound as stated.** The only P4 item is the documentation note about `R > 0` being the physical regime (negative `R` gives trivial zero probability, not an error). No rewrite needed.
