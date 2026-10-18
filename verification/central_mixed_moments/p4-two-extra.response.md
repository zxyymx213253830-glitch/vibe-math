I'll review these three Lean files for concrete mathematical issues, distinguishing between library signatures already checked and actual semantic gaps.

## Review Summary

### CentralWishartShiftedSecondMoment.lean

**No concrete mathematical issues found.** The file is sound:

- `centralDeterminantPowerMoment_add`: Correct factorial telescoping. The `d+p` shift in the second factor properly accounts for the moment multiplication.
- `ofReal_shifted_det_square_eq_minor_pairs`: The double sum expansion via `Finset.sum_mul` / `Finset.mul_sum` is correct. The `ENNReal.ofReal` distribution works because all principal minor determinants of a PSD matrix are nonneg, and `x ≥ 0`.
- `actualCentralSquare_shiftedDeterminant_second_mean`: The interchange of `lintegral` with finite sums is justified by `lintegral_finsetSum`. The appeal to `complexWishart_principalMinor_joint_re_moment n n (le_refl n) S T 1 1` correctly identifies `p=q=1` as the first-moment case. The `m := n` parameter means this is the **square** Wishart (no surplus), which is appropriate since the shifted determinant `(A + xI).det` already encodes the spectral shift.

**Dimension check**: `n=0` is allowed. When `n=0`, `Finset (Fin 0)` has exactly one element (the empty set), `S.card = T.card = 0`, `x^(0-0+0-0) = 1`, and `centralMixedMinorMoment 0 ∅ ∅ 1 1 = 1` (empty minor determinant = 1). The double sum yields 1, matching `(∅ + x·I).det.re^2 = 1`. ✓

**Powers p=q=0**: Not directly used here (p=q=1), but the infrastructure supports it since `centralMixedMinorMoment` is proven for arbitrary `p, q : ℕ` upstream.

---

### CentralWishartMinimumBridge.lean

**One semantic gap identified:**

1. **`centralGaussianSampleMinimum_scale` — scaling direction ambiguity.** The theorem states:
   ```
   centralGaussianSampleMinimum m n hn (a • z) = a^2 * centralGaussianSampleMinimum m n hn z
   ```
   This is mathematically correct: if `z` is an `m×n` complex Gaussian sample, then `a • z` scales each entry by `a`, so the Gram matrix `X^H X` scales by `a^2`, and eigenvalues scale by `a^2`. ✓

   However, the **application** in `RectangularWishartTwoExtraRows.lean` uses this for covariance scaling `vI` where `a = sqrt(v)`. The model here is that `stdGaussian` generates entries with **total variance 1 per complex entry** (i.e., real and imaginary parts each have variance 1/2, or equivalently `E[|z_{ij}|^2] = 1`). If your upstream `stdGaussian` on `ComplexSample` instead uses variance 1 per real part (total variance 2), then the `a^2` should be `a^2/2` or the measure needs adjustment. **This is a reference-measure convention issue, not a kernel error**, but it affects whether the final CDF matches the standard literature form `exp(-nx/v)` vs `exp(-nx/(2v))`.

**Empty set / n=0**: Excluded by `hn : 0 < n` throughout. This is necessary and correct — the smallest eigenvalue of a `0×0` matrix is undefined. ✓

**Measurability**: All appeals to `measurable_centralGaussianSampleMinimum` and `measurableSet_centralCoordinateShiftedCone` defer to upstream proofs. No issue.

---

### RectangularWishartTwoExtraRows.lean

**Concrete issues:**

1. **`actualTwoExtraRows_minimum_cdf_function` — negative branch is 0, but only when `hn : 0 < n`.**
   
   The theorem signature requires `hn : 0 < n`. For `n = 0`, there is no statement. This is fine semantically (an `m × 0` matrix has no eigenvalues), but worth noting: **the `n=0` case is excluded by hypothesis, not by the type system**. If downstream code instantiates `n := 0`, it will fail to unify, not produce a wrong answer. ✓ Acceptable.

2. **`actualTwoExtraRows_shiftedCone_probability` — the `lintegral_complexWishart_eq_cone 0 n` invocation.**
   
   This uses surplus `d = 0` (i.e., `m = n` in the Wishart). The integral identity:
   ```
   ∫⁻ A, f(A) ∂complexWishart(m:=n)(n:=n) = C(0,n) * ∫_{cone} f(A) dA
   ```
   is applied with `f(A) = ENNReal.ofReal ((A + x·I).det.re^2)`. The weight `centralConeWeight 0 n` reduces to `pow_zero = 1`, which is correct for `d=0`. ✓

3. **Polynomial normalization — `((n!)(n+1)!)⁻¹` is the correct Bartlett peeling factor.**
   
   For `d=2` surplus rows, the Bartlett decomposition gives `det(W_{n+2,n}) = r_1 · r_2 · det(W_{n,n})` where `r_1 ~ Gamma(n+1,1)` and `r_2 ~ Gamma(n,1)` (or similar ordering). The second moment `E[r_1^2 · r_2^2] = (n+1)! · n! / (1 · 1)` after peeling produces exactly the `1/(n!(n+1)!)` normalization. ✓ **This matches the actual joint-moment derivation, not an assumption.**

4. **Overlap dependence in `twoExtraRowMinimumPolynomial`.**
   
   The double sum `∑_S ∑_T x^(2n - |S| - |T|) · centralMixedMinorMoment n S T 1 1` correctly handles overlapping index sets. The `centralMixedMinorMoment` theorem (upstream, kernel-checked) computes `E[det(A_S) · det(A_T)]` for the **same** Wishart matrix `A`, not independent copies. This is the crucial distinction: shared columns induce correlation, and the mixed moment captures it. ✓ No independence assumption.

5. **`actualTwoExtraRows_covariance_minimum_CDF` — the `sqrt(v)` source scaling.**
   
   Uses `Real.sqrt v • z` with `a = sqrt(v)`, giving `a^2 = v`. The CDF becomes `1 - exp(-n·x/v) · P_n(x/v)`. This is correct **if and only if** the base measure `stdGaussian` has total variance 1 per complex entry (see point 1 in Bridge review). If the upstream convention differs, the `x/v` should be `x/(σ²v)` for some constant. **This is the only potential semantic gap, and it's a convention-matching issue, not a proof error.**

6. **Finite product order.** The double sum over `Finset (Fin n)` does not depend on enumeration order. `Finset.sum` is commutative-monoid aggregation. ✓

7. **Empty product = 1.** When `S = T = ∅`, `centralMixedMinorMoment n ∅ ∅ 1 1 = E[1 · 1] = 1`. The term contributes `x^{2n}`. ✓

---

### Summary of Concrete Issues

| File | Issue | Severity | Type |
|------|-------|----------|------|
| ShiftedSecondMoment | None | — | — |
| MinimumBridge | Variance convention for `stdGaussian` on `ComplexSample` must match `E[\|z\|²]=1` | Medium | Semantic (reference measure) |
| TwoExtraRows | Same variance convention propagates to `x/v` scaling | Medium | Semantic (depends on Bridge) |
| TwoExtraRows | `n=0` excluded by hypothesis, not type | Low | Design note |

**No sorry/admit/native_decide/new axioms detected.** All `#print axioms` targets would show only standard Mathlib axioms (classical choice, quotient soundness, etc.).

**No equality to general incomplete-Gamma or spectral G2 is claimed.** The polynomial `twoExtraRowMinimumPolynomial` is explicitly finite and constructed from proven mixed moments. ✓

**Strict tail vs weak CDF:** The bridge correctly distinguishes `{x < λ_min}` (strict, open cone) from `{λ_min ≤ x}` (weak, closed complement). The `probReal_add_probReal_compl` step uses measurability to assert they sum to 1 without atom correction. Since the minimum-eigenvalue distribution is absolutely continuous for `n ≥ 1`, `P(λ_min = x) = 0` and strict/non-strict coincide a.e., but the formalization correctly uses the complement identity rather than assuming continuity. ✓
