# P4 Issues-Only Review

## Concrete Issues

### 1. Missing `r > 0` hypothesis in `actualCorrelatedMatrixLogDet_low_scale_curvature`

The second-order theorem divides by `r^2` and takes `𝓝[>] 0`, but the spectral identity substitution uses `hrp.le` (i.e., `0 ≤ r`). When `r = 0`, the division `(...)/r^2` is undefined. The first-order theorem correctly has `hr : 0 < r` from `self_mem_nhdsWithin`, but the curvature theorem needs to ensure `r ≠ 0` or explicitly require `0 < r` before rewriting via `actualCorrelatedMatrixLogDet_eq_spectral`. Currently `hrp : 0 < r` is obtained, so this is actually fine—the issue is cosmetic, not a bug. **Retract: no issue here.**

### 2. Type mismatch risk in `sum_integral_actualCorrelatedEigenvalue_sq_closed` RHS

The RHS mixes `(m : ℝ)` and `(m : ℂ)` coercions:
```lean
(((m : ℂ) • complexGram B+complexGram M)^2).trace.re + (m : ℝ)*(complexGram B).trace.re^2 + ...
```
The first term extracts `.re` from a complex-trace, but the second term scales by `(m : ℝ)`. This is mathematically correct, but if `integral_actualCorrelatedGram_squaredTrace` returns the fully complex-coerced form `(m : ℂ)`, the `norm_num`/`ring` closure in downstream files may fail to unify `(m : ℝ)` with `((m : ℂ)).re`. Verify that `integral_actualCorrelatedGram_squaredTrace`'s output matches this mixed-coercion pattern exactly, or standardize to `(m : ℝ)` throughout after taking `.re`.

### 3. `finiteSpectrumLogDet` integrability composition gap

In `integrable_actualCorrelatedMatrixLogDet`, the proof applies `integrable_finsetSum` with `integrable_log_one_add_mul`. This requires that each `actualCorrelatedEigenvalue B M i` is integrable **and** that the logarithm composition preserves integrability. The call `integrable_log_one_add_mul _ _ (integrable_actualCorrelatedEigenvalue B M i) ... r hr` passes the eigenvalue integrability, but the domination condition for `log(1 + r*λ)` as `r → 0⁺` needs `|log(1+r*λ)| ≤ C*r*λ` uniformly. This holds for `r ∈ (0,1]` and `λ ≥ 0`, but the constant `C` depends on the upper bound of `r*λ`. If the imported `integrable_log_one_add_mul` doesn't internally handle this uniformity, the integrability claim is incomplete. **Check the exact statement of `integrable_log_one_add_mul`**—if it requires only `Integrable f` and `ae 0 ≤ f`, then this is fine.

### 4. Eigenvalue indexing ambiguity: `Fin (Fintype.card (Fin n))` vs `Fin n`

`actualCorrelatedEigenvalue` indexes by `Fin (Fintype.card (Fin n))`, which equals `Fin n` definitionally but not syntactically. The equivalence `e` in `sum_actualCorrelatedEigenvalues_eq_trace` handles this, but every downstream use must transport across this equivalence. If any imported theorem (e.g., `hermitian_trace_square_eq_orderedEigenvalues`) expects indexing by `Fin n` directly, the rewrite `he` will fail to typecheck. Confirm that `hermitian_trace_square_eq_orderedEigenvalues` accepts `Fin (Fintype.card (Fin n))` or add an explicit `Equiv.sum_comp` transport in `sum_integral_actualCorrelatedEigenvalue_sq_closed`.

### 5. `gram_real_logdet_eq_spectral` domain requirement

`actualCorrelatedMatrixLogDet_eq_spectral` calls `gram_real_logdet_eq_spectral (complexSampleMatrix z*B+M) r hr` with `hr : 0 ≤ r`. If `gram_real_logdet_eq_spectral` was proved only for `r > 0` (strict), then passing `hr.le` at `r = 0` would be invalid. Check whether the imported theorem allows `r = 0`—at `r = 0`, both sides equal `log 1 = 0`, so it should hold, but only if the formalized statement includes `r = 0`.

### 6. No measurability proof for `fun z => finiteSpectrumLogDet (...) r`

The rewrite `he` in the low-scale theorems substitutes `actualCorrelatedMatrixLogDet` with the spectral sum, but the integral `∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _` requires measurability of the integrand. The file proves `measurable_actualCorrelatedEigenvalue` but never states `Measurable (actualCorrelatedMatrixLogDet B M r)`. It's inferred via `actualCorrelatedMatrixLogDet_eq_spectral` and composition, but if `finiteSpectrumLogDet` isn't registered as measurable in the imports, the integral is ill-typed. Add an explicit `measurable_actualCorrelatedMatrixLogDet` lemma or confirm the import provides it.

---

## Non-Issues Confirmed Checked

- **Weyl continuity**: Uses `orderedHermitianEigenvalueCoordinatesContinuous`, no axiom.
- **Zero/singular B, M**: All bounds use `≤ trace` and nonnegativity, no inverse moments.
- **Natural log**: `Real.log` used consistently.
- **Rectangular dimensions**: `m×p` Z, `p×n` B, `m×n` M handled correctly.
- **No high-SNR/rank claims**: Absent.
- **Domination for first/second order**: Eigenvalue L1/L2 integrability proven via trace domination.
