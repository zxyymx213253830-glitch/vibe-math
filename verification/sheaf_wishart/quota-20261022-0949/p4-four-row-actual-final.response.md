# P4 Adversarial Review

## Source 1: `OneColumnRadialCDF.lean`

**Mathematical gap (kernel integral domain).** The proof of `hs : L + T = 1` invokes `intervalIntegral.integral_interval_add_Ioi` to glue `Ioc 0 b` and `Ioi b` into `Ioi 0`, then applies `noncentralChiEvenRadialKernel_integral_eq_one`. That normalization theorem must assert integration over `Ioi 0` (or the full half-line). If it instead states the integral over `univ` or `[0, ∞)`, the point `{0}` has measure zero only when the kernel is locally integrable there—a condition not stated. Confirm the exact domain in the imported lemma.

**Mathematical gap (`t = 0` underflow).** The theorem signature allows `t : ℕ` with `ht : 1 ≤ t`. Inside the proof, `ht' : t - 1 + 1 = t` uses truncated subtraction. This is correct for `t ≥ 1`, but the kernel index `q := t - 1` becomes `0` when `t = 1`. Verify that `nuttallQ_succ_self_tail_norms` and `noncentralChiEvenRadialKernel` are defined and normalized for `q = 0`; otherwise the base case is silently unsupported.

**API-level question (not a gap).** `evenKernelNonneg` unfolds the kernel and applies `tsum_nonneg (fun n => by positivity)`. This requires every summand to be non-negative pointwise. The kernel presumably contains factors like `(a * r)^(2n)` or similar even-power terms. Without seeing the definition, I cannot confirm the `positivity` tactic discharges all cases—this is an API trust issue, not a logical error, but flag it if the kernel has alternating-sign components.

**Minor.** `Complex.norm_of_nonneg` requires a real, non-negative argument cast to `ℂ`. The proof supplies `mul_nonneg (pow_nonneg ha.le _) hTn`, which is fine since `ha : 0 < a` gives `0 ≤ a`. No gap.

---

## Source 2: `Theorem12FourRowsActualCDF.lean`

**Mathematical gap (lambda scope collision).** The `let lambda := ...` shadows any outer binding. The call to `theorem12OneColumnCandidates_eq_radialCDF 4 (by omega) lambda x hEnergy hx` passes this `lambda` as the scalar parameter. The imported theorem expects `hl : 0 < lambda`, which here is exactly `hEnergy`. This is consistent, but the proof uses `hEnergy` directly rather than re-deriving `0 < lambda` after the `let`—technically fine since they're definitionally equal, but fragile if the `let` is refactored.

**Mathematical gap (norm map identity).** `hnorm` relies on two claims chained: `fourRowSampleToFin8.norm_map` and `complexSampleMean_oneColumn_norm_sq_eq_twice_frobenius M`. The latter asserts `‖mean(M)‖² = 2 * ‖M‖_F²` for a 4×1 matrix. For a one-column matrix, `‖M‖_F² = Σᵢ ‖M i 0‖²`, and the mean vector's squared norm should equal this sum (not twice it) under standard conventions. The factor of 2 suggests a specific `ComplexSample → Fin 8` real-embedding convention doubling the norm. **This is the critical semantic check**: if the Frobenius convention in `OneColumnFrobeniusParameter` does not include this factor-of-2 embedding, then `hnorm` is wrong and the entire CDF identification fails.

**Mathematical gap (hardcoded indices).** The theorem hardcodes `m = 4, n = 1, t = 4` while calling `theorem12OneColumnCandidates_eq_radialCDF 4 (by omega)`. The imported theorem is general in `t`; verify that `q = t - 1 = 3` matches the kernel index used in `noncentralFourRowCDF_eq_radialSeries_of_mean`. A mismatch between the sample dimension (4 rows) and the Bessel/kernel order (3) would indicate an off-by-one error in the mathematical mapping.

**No gap (measure/model conditions).** The CDF `F` is defined via `stdGaussian (ComplexSample ...)` pushed through `complexNoncentralSampleSmallestEigenvalue M`. The stochastic model is explicit; no hidden positivity or finite-measure assumptions are needed beyond what `stdGaussian` provides.
