## P4 Adversarial Review: `ActualSingularPositiveLogSquare.lean`

### 1. Actual Mathematical Gaps

**Gap 1 (Critical): Pointwise bound `|S z| ≤ T z + C + 2*|A z|` lacks justification when eigenvalues are zero.**

The proof invokes `abs_positive_log_sum_le_minor_log` with witness `hz` from `hne`. However, `positiveSpectrumLog` is defined as `log(λ)` on `λ > 0` and `0` on `λ = 0`. The sum `S z` runs over *all* indices `i`, but the minor-log bound `A z` controls only the product of *nonzero* eigenvalues via the rank-`r` minor determinant. 

The hypothesis `hz` from `hne` (the AE-witness) must explicitly guarantee that the zero-eigenvalue terms contribute nothing to `S z` and that the nonzero terms biject with the minor's spectrum. If `hz` merely asserts `rank = r` without controlling the alignment between `positiveSpectrumLog`'s support and the minor's nonzero spectrum, the pointwise inequality `|S z| ≤ T z + C + 2*|A z|` is **unjustified**. The proof treats this as a black-box implication; it is not algebraically trivial.

**Gap 2 (Moderate): Third theorem's variance identity silently assumes finite measure / probability normalization.**

The centered second moment theorem expands `(S - ∫S)²` and uses `integral_const` to conclude `∫a² = a²`. This requires `stdGaussian _` to be a **probability measure** (total mass 1). While Gaussian measures are typically normalized, the statement never explicitly asserts `[IsProbabilityMeasure (stdGaussian _)]` or equivalent. If `stdGaussian` is an unnormalized Gaussian reference measure, then `∫a² dμ = a² · μ(univ) ≠ a²`, and the variance decomposition fails. The integrability hypotheses (`hS`, `hQ`) do not imply normalization.

**Gap 3 (Minor): Measurability of `positiveSpectrumLog` composition.**

The measurability proof unfolds `positiveSpectrumLog` and applies `Measurable.ite` on `{λ > 0}`. This requires that `measurable_actualCorrelatedEigenvalue B M i` produces a measurable function into `ℝ` (not just `ℂ`), and that eigenvalues are guaranteed real. If `actualCorrelatedEigenvalue` returns `ℂ` and coercion/comparison with `0 : ℝ` is implicit, the measurable set `{z | eigenvalue B M i z > 0}` needs justification that the eigenvalue is real-valued AE or everywhere.

---

### 2. Non-Issues (Acknowledged)

- **Imported results** (`integrable_actualAffineCompressedDet_log_sq`, `sum_actualCorrelatedEigenvalues_eq_trace`, `integrable_actualCorrelatedGram_trace_sq`, etc.) are treated as separately verified dependencies. No signature requests needed—their semantic roles match usage.
- **The domination argument** `(S z)² ≤ 3T² + 3C² + 12A²` via `nlinarith` is arithmetically valid given the pointwise bound.
- **Second theorem's reduction** to first via `abs_positiveSpectrumLog_le_trace_add_abs_sum` is structurally sound assuming nonnegativity of eigenvalues (explicitly passed as hypothesis).

---

### Summary

| # | Severity | Issue | Type |
|---|----------|-------|------|
| 1 | Critical | Minor-log pointwise bound requires explicit AE-witness semantics for zero-mode alignment | Math gap |
| 2 | Moderate | Variance identity assumes probability normalization not stated in assumptions | Math gap |
| 3 | Minor | Real-valuedness/coercion in eigenvalue measurability | Math gap |
